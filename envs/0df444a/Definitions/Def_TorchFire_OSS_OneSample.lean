-- Prove2me | Definitions.Def_TorchFire_OSS_OneSample
-- name    : TorchFire_OSS_OneSample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:33:24.04068+00:00
-- url     : https://prove2.me/theorems/ad22d2ae-580f-4816-85ec-aaadcd4793e8
-- title:
--   The oracle distribution of Construction 4.2: $\pi$, $A_y$, $b_y$, cosets $W_y$, $P$, $P^{-1}$, $D$
-- statement:
--   **Construction 4.2** ([SZ25, Construction 28]). For $\lambda\ge2$ set $r=16\lambda(\lambda-1)$, $n=r+24\lambda$, $k=n$ (4). A sample is a uniform permutation $\pi$ of $\{0,1\}^n$, written $\pi(x)=(H(x),J(x))$ with $|H(x)|=r$, and, independently for each $y\in\{0,1\}^r$, a uniform full-rank matrix $A_y\in\mathbb Z_2^{k\times(n-r)}$ and a uniform vector $b_y\in\mathbb Z_2^k$. The subspace and coset are $S_y=\{A_yw\}$ and $W_y=b_y+S_y$ (5). The public collection $O=(P,P^{-1},D)$ (6) is
--   $$P(x)=(H(x),A_{H(x)}J(x)+b_{H(x)}),\quad P^{-1}(y,u)=\begin{cases}\pi^{-1}(y,w)&u=A_yw+b_y\\\perp&\text{otherwise}\end{cases},\quad D(y,v)=1[v^{\mathsf T}A_y=0^{n-r}],$$
--   and the coset state is $|W_y\rangle=2^{-(n-r)/2}\sum_w|A_yw+b_y\rangle$ (7). The public collection is one combined oracle with $P^{-1}$'s ⊥ flag.
--
--   **Formalization Note** Every parameter is taken at $\max(\lambda,2)$ (paper.md decision 7), so the construction is defined for all $\lambda$ and is the paper's for $\lambda\ge2$. Full rank of a $k\times(n-r)$ matrix with $k>n-r$ is full column rank (Fact 4.4).
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Construction 4.2 (4)–(6) p.20, Fact 4.4, Definition 4.5 (7) p.20

import Mathlib
import Definitions.Def_TorchFire_Model_xorOracle

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model

namespace TorchFire.OSS

/-- The effective security parameter `max(λ, 2)` (paper.md decision 7): Construction 4.2 is stated
"For `λ ≥ 2`" (p.20), and every construction at `λ` is the paper's construction at `max(λ, 2)`.
Negligibility does not see finitely many `λ`, and every statement with an explicit bound assumes
`λ ≥ 2`, where `eff λ = λ`. -/
def eff (lam : ℕ) : ℕ := max lam 2

/-- `r = 16λ(λ − 1)` (4), p.20. -/
abbrev r (lam : ℕ) : ℕ := 16 * eff lam * (eff lam - 1)

/-- `n − r = 24λ` (4), p.20: the dimension of the inverse coordinate `w ∈ Z_2^{n−r}`. -/
abbrev nr (lam : ℕ) : ℕ := 24 * eff lam

/-- `n = r + 24λ` (4), p.20. -/
abbrev n (lam : ℕ) : ℕ := r lam + nr lam

/-- `k = n` (4), p.20. -/
abbrev k (lam : ℕ) : ℕ := n lam

/-- A full-rank `k × (n − r)` matrix over `Z_2`. Since `k > n − r`, full rank is full column rank
(Fact 4.4, p.20: "Full column rank makes the inverse coordinate `w` unique"), i.e. `w ↦ A w` is
injective. -/
def FullRank (lam : ℕ) : Type :=
  {A : Matrix (Fin (k lam)) (Fin (nr lam)) (ZMod 2) // Function.Injective A.mulVec}

noncomputable instance (lam : ℕ) : Fintype (FullRank lam) := by
  unfold FullRank; exact Fintype.ofFinite _

noncomputable instance (lam : ℕ) : DecidableEq (FullRank lam) := by
  unfold FullRank; exact Classical.decEq _

/-- **The oracle distribution of Construction 4.2** (Chatterjee–Mukherjee–Pathak–Podder, *Quantum
Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593, p.20,
[SZ25, Construction 28]). A sample is a permutation `π` of `{0,1}^n`, a full-rank matrix
`A_y ∈ Z_2^{k×(n−r)}` and a vector `b_y ∈ Z_2^k` for every `y ∈ {0,1}^r`. The distribution is
uniform on this finite set (independent uniform `π`, `A_y`, `b_y`). -/
abbrev OneSample (lam : ℕ) : Type :=
  Equiv.Perm (Bits (n lam)) × (Bits (r lam) → FullRank lam) × (Bits (r lam) → Bits (k lam))

variable {lam : ℕ}

/-- `π(x) = (H(x), J(x))`, `|H(x)| = r` (p.20). -/
def Hx (ω : OneSample lam) (x : Bits (n lam)) : Bits (r lam) :=
  fun i => ω.1 x (Fin.castAdd (nr lam) i)

/-- `π(x) = (H(x), J(x))`, `|J(x)| = n − r` (p.20). -/
def Jx (ω : OneSample lam) (x : Bits (n lam)) : Bits (nr lam) :=
  fun i => ω.1 x (Fin.natAdd (r lam) i)

/-- The matrix `A_y`. -/
def Amat (ω : OneSample lam) (y : Bits (r lam)) : Matrix (Fin (k lam)) (Fin (nr lam)) (ZMod 2) :=
  (ω.2.1 y).1

/-- The shift `b_y`. -/
def bvec (ω : OneSample lam) (y : Bits (r lam)) : Bits (k lam) := ω.2.2 y

/-- **The coset** `W_y = b_y + S_y`, `S_y = {A_y w : w ∈ Z_2^{n−r}}` (5), p.20. -/
def InCoset (ω : OneSample lam) (y : Bits (r lam)) (u : Bits (k lam)) : Prop :=
  ∃ w : Bits (nr lam), (Amat ω y).mulVec w + bvec ω y = u

/-- `P(x) = (H(x), A_{H(x)} J(x) + b_{H(x)})` (6), p.20. -/
def P (ω : OneSample lam) (x : Bits (n lam)) : Bits (r lam) × Bits (k lam) :=
  (Hx ω x, (Amat ω (Hx ω x)).mulVec (Jx ω x) + bvec ω (Hx ω x))

/-- `P⁻¹(y, u) = π⁻¹(y, w)` if `u = A_y w + b_y` for some `w`, and `⊥` otherwise (6), p.20. By full
column rank the `w` is unique (Fact 4.4). -/
noncomputable def Pinv (ω : OneSample lam) (p : Bits (r lam) × Bits (k lam)) :
    Option (Bits (n lam)) :=
  by classical exact
    if h : InCoset ω p.1 p.2 then some (ω.1.symm (Fin.append p.1 (Classical.choose h))) else none

/-- `D(y, v) = 1[vᵀ A_y = 0^{n−r}]` (6), p.20. -/
noncomputable def D (ω : OneSample lam) (p : Bits (r lam) × Bits (k lam)) : ZMod 2 :=
  by classical exact if Matrix.vecMul p.2 (Amat ω p.1) = 0 then 1 else 0

/-- **The coset superposition state** (7), Definition 4.5, p.20:
`|W_y⟩ = 2^{−(n−r)/2} Σ_{w ∈ Z_2^{n−r}} |A_y w + b_y⟩`. -/
noncomputable def cosetState (ω : OneSample lam) (y : Bits (r lam)) : Bits (k lam) → ℂ :=
  fun u => ∑ w : Bits (nr lam),
    if (Amat ω y).mulVec w + bvec ω y = u then (((Real.sqrt 2 : ℝ) : ℂ) ^ nr lam)⁻¹ else 0

/-- The query domain of the public collection `O = (P, P⁻¹, D)` (6): forward queries `x`, inverse
queries `(y, u)` and dual queries `(y, v)`. -/
abbrev PubDom (lam : ℕ) : Type :=
  Bits (n lam) ⊕ (Bits (r lam) × Bits (k lam)) ⊕ (Bits (r lam) × Bits (k lam))

/-- The answer register of the public collection: one slot per component, `P⁻¹` with its ⊥ flag. -/
abbrev PubAns (lam : ℕ) : Type :=
  (Bits (r lam) × Bits (k lam)) × (ZMod 2 × Bits (n lam)) × ZMod 2

/-- **The public oracle collection `O = (P, P⁻¹, D)`** of Construction 4.2 (6), p.20, as one
combined oracle (paper.md decision 3). None of `π`, `A_y`, `b_y` is otherwise accessible
(Fact 4.3). -/
noncomputable def pubOracle (ω : OneSample lam) : PubDom lam → PubAns lam :=
  combine (P ω) (combine (fun p => encBot (Pinv ω p)) (D ω))

instance (lam : ℕ) : Fintype (PubDom lam) := inferInstance
instance (lam : ℕ) : DecidableEq (PubDom lam) := inferInstance
instance (lam : ℕ) : Fintype (PubAns lam) := inferInstance
instance (lam : ℕ) : DecidableEq (PubAns lam) := inferInstance
noncomputable instance (lam : ℕ) : Fintype (OneSample lam) := inferInstance

end TorchFire.OSS


