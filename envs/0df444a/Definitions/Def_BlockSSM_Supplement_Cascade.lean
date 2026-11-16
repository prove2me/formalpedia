-- Prove2me | Definitions.Def_BlockSSM_Supplement_Cascade
-- name    : BlockSSM_Supplement_Cascade
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:03:19.556279+00:00
-- url     : https://prove2.me/theorems/a886c3f4-d4aa-4420-8595-dd44f9730a22
-- title:
--   Finite-state cascades of block-diagonal layers
-- statement:
--   A **layer** over an alphabet $\Sigma$ with block bound $b$ consists of a block partition with blocks of size at most $b$, for each symbol $x\in\Sigma$ block-diagonal matrices and a bias (an affine map $h\mapsto A_xh+c_x$), and a start state; it has no decoder.
--
--   A **depth-$k$ cascade** stacks $k$ layers, each over its own finite alphabet $\Sigma_j$, with $\Sigma_1=G$ the input alphabet. At time $t$ layer one reads $u^1_t=x_t$; after its update to $h^j_t$, layer $j$ passes
--   $$
--   u^{j+1}_t=\psi_j(h^j_t,u^j_t)\in\Sigma_{j+1}
--   $$
--   to the next layer, for an arbitrary map $\psi_j$; there is no other memory across time. The cascade is **finite-state** if the set of reachable stack states $(h^1_t,\dots,h^k_t)$ is finite, it **tracks** $G$ if some decoder on the full stack returns $x_T\cdots x_1$ after every prefix (the empty one included), and its **total dimension** is the sum of the layers' hidden dimensions. The **least cascade depth** at block size $b$ is the least $k$ for which a finite-state depth-$k$ cascade tracks $G$, or $\infty$.
--
--   This is the model of the depth theorem, Theorem 16.
--
--   **Formalization Note** A cascade is an inductive stack: the empty stack, or a layer over $\Sigma$ with an interface into a finite alphabet $\Sigma'$ followed by a cascade over $\Sigma'$. Depth $0$ (the empty stack, constant decoder) is allowed.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), §8, pp.7–8 (PDF pp.8–9)

import Mathlib
import Definitions.Def_BlockSSM_Tracker
import Definitions.Def_BlockSSM_wordProd

universe u

namespace BlockSSM.Supplement

open BlockSSM

/-- **A cascade layer.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), §8, p.7 (PDF p.8): a layer "of the form in section 2" over its own
alphabet `Sym`: a block partition with every block of size at most `b` (fixed across symbols), for
every symbol block matrices and a bias, and a start state. A layer has no decoder of its own.

**Formalization Note.** The same data as `BlockSSM.Tracker` without the decoder; `b : ℕ∞`. -/
structure Layer (Sym : Type u) (b : ℕ∞) where
  /-- The number of blocks. -/
  m : ℕ
  /-- The block sizes. -/
  n : Fin m → ℕ
  /-- Every block has size at most `b`. -/
  n_le : ∀ i, (n i : ℕ∞) ≤ b
  /-- The block matrices. -/
  A : Sym → ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ
  /-- The biases. -/
  c : Sym → State n
  /-- The start state. -/
  h₀ : State n

/-- The affine update `h ↦ A_x h + c_x` of a layer on reading `x`. -/
def Layer.step {Sym : Type u} {b : ℕ∞} (L : Layer Sym b) (x : Sym) (h : State L.n) : State L.n :=
  fun i => (L.A x i).mulVec (h i) + L.c x i

/-- The hidden dimension of a layer. -/
def Layer.hiddenDim {Sym : Type u} {b : ℕ∞} (L : Layer Sym b) : ℕ := ∑ i, L.n i

/-- **Depth-`k` cascade.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), §8, pp.7–8 (PDF pp.8–9): "A depth-k cascade stacks finite-state
layers of the form in section 2, each over its own finite alphabet Σ_j. Layer one reads u¹_t = x_t.
After its update, layer j passes u^{j+1}_t = ψ_j(h^j_t, u^j_t) to the next layer, for an arbitrary
map into the next finite alphabet. A decoder sees the full stack. The interface may forward the
current input symbol, but has no extra memory across time."

`Cascade b Sym k` is a stack of `k` layers whose first layer reads the alphabet `Sym`: `nil` is the
empty stack, and `cons L Sym' _ ψ rest` puts the layer `L` over `Sym` on top of the cascade `rest`
over the finite alphabet `Sym'`, with interface `ψ : State L.n → Sym → Sym'`.

**Formalization Note.** The alphabet of the first layer is the input alphabet itself (for tracking,
`Σ₁ = G`). Every later alphabet is finite (the field `Finite Sym'`). Finite-stateness and the
decoder are not part of the data: see `Cascade.IsFiniteState` and `Cascade.Tracks`. -/
inductive Cascade (b : ℕ∞) : Type u → ℕ → Type (u + 1) where
  /-- The empty stack (depth `0`). -/
  | nil (Sym : Type u) : Cascade b Sym 0
  /-- A layer over `Sym` with interface `ψ` into the finite alphabet `Sym'` of the remaining stack. -/
  | cons {Sym : Type u} {k : ℕ} (L : Layer Sym b) (Sym' : Type u) (hfin : Finite Sym')
      (ψ : State L.n → Sym → Sym') (rest : Cascade b Sym' k) : Cascade b Sym (k + 1)

namespace Cascade

variable {b : ℕ∞}

/-- The state of the full stack `(h¹, …, h^k)`. -/
def StackState : {Sym : Type u} → {k : ℕ} → Cascade b Sym k → Type
  | _, _, nil _ => PUnit
  | _, _, cons L _ _ _ rest => State L.n × rest.StackState

/-- One time step on input `x`: layer one updates on `x` to `h¹_t`, passes `ψ₁(h¹_t, x)` to the
next layer, and so on down the stack. -/
def step : {Sym : Type u} → {k : ℕ} → (C : Cascade b Sym k) → Sym → C.StackState → C.StackState
  | _, _, nil _, _, s => s
  | _, _, cons L _ _ ψ rest, x, s => (L.step x s.1, rest.step (ψ (L.step x s.1) x) s.2)

/-- The start state of the stack. -/
def start : {Sym : Type u} → {k : ℕ} → (C : Cascade b Sym k) → C.StackState
  | _, _, nil _ => PUnit.unit
  | _, _, cons L _ _ _ rest => (L.h₀, rest.start)

/-- The total hidden dimension `∑_j dim(layer j)`. -/
def totalDim : {Sym : Type u} → {k : ℕ} → Cascade b Sym k → ℕ
  | _, _, nil _ => 0
  | _, _, cons L _ _ _ rest => L.hiddenDim + rest.totalDim

/-- The stack state after reading the word `s = [x₁, …, x_T]` (first letter first). -/
def run {Sym : Type u} {k : ℕ} (C : Cascade b Sym k) (s : List Sym) : C.StackState :=
  s.foldl (fun h x => C.step x h) C.start

/-- The cascade is finite-state: its whole-stack reachable set is finite. -/
def IsFiniteState {Sym : Type u} {k : ℕ} (C : Cascade b Sym k) : Prop :=
  (Set.range C.run).Finite

/-- The cascade tracks the group `G`: some decoder on the full stack returns the running product
`x_T ⋯ x₁` after every prefix, the empty one included. -/
def Tracks {G : Type u} [Group G] {k : ℕ} (C : Cascade b G k) : Prop :=
  ∃ dec : C.StackState → G, ∀ s : List G, dec (C.run s) = wordProd s

end Cascade

/-- **The least cascade depth.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 16, p.8 (PDF p.9): "the least finite-state cascade
depth at block size at most b that tracks G".

**Formalization Note.** Infimum in `ℕ∞`, `⊤` if no finite-state cascade tracks `G`; depth `0` (the
empty stack with a constant decoder) is allowed. -/
noncomputable def cascadeDepth (G : Type u) [Group G] (b : ℕ∞) : ℕ∞ :=
  sInf {D : ℕ∞ | ∃ (k : ℕ) (C : Cascade b G k), D = (k : ℕ∞) ∧ C.Tracks ∧ C.IsFiniteState}

end BlockSSM.Supplement


