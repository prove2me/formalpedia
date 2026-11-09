-- Prove2me | Definitions.Def_WeightedSpectralSketch_LowerBound_Anchor
-- name    : WeightedSpectralSketch_LowerBound_Anchor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:08:46.499064+00:00
-- url     : https://prove2.me/theorems/cf845372-726c-40f6-91d9-daa46bf1e3d1
-- title:
--   The anchored hard distributions (12), anchor-goodness and the incidence dimension $K(C)$ (§6)
-- statement:
--   Fix $b\ge2$ and an even $\ell\ge2$, and let $|V|=n=2\ell b$. The **anchored template** has $\ell b$ anchor slots and $\ell$ ring blocks of $b$ slots; an anchored labeling $\pi$ is a bijection from these slots to $V$. The anchor $C$ is the set of vertices in anchor slots, the ring is $R=V\setminus C$, so $|C|=|R|=\ell b$, and the query $q=xy$ joins the distinguished slots $(0,j_x)$ and $(\ell/2,j_y)$ of the ring.
--
--   1. **Base weights** (Eq. (12)), with $w_{\mathrm{int}}=n^2$ and $w_{\mathrm{ext}}=\ell/(16b^2)$: $w_e=w_{\mathrm{int}}$ for $e\in\binom C2$ or $e$ inside a ring block, $w_e=w_{\mathrm{ext}}L(i,j)^{-4}$ between ring blocks $B_i\ne B_j$, and $w_e=0$ between $C$ and $R$.
--   2. **Inputs:** No gives $\tilde w_e=w_ez_e$ and Yes gives $\tilde w_e=w_ez_e+\mathbf 1\{e=q\}$; coordinates of weight $0$ stay $0$. The **support** is the set of all such inputs with every $z_e\in[\tfrac12,\tfrac32]$.
--   3. For a sketch matrix $A=[a_e]$ and a set $C$: $A_C=[a_e:e\in\binom C2]$ and $A_{v,C}=[a_{vw}:w\in C]$. A pair $uv$ is **anchor-good** if $\mathrm{lev}_{a_{uv}}([A_{u,C}\,A_{v,C}\,A_C])\le1$.
--   4. $k_v(C)=n_+\big(A_{v,C}A_{v,C}^\top-A_CA_C^\top\big)$, the number of strictly positive eigenvalues counted with multiplicity, and $K(C)=\sum_{v\in R}k_v(C)$.
--
--   The heavy, disconnected anchor clique lets an arbitrary sketch be reduced to an incidence sketch on the ring of expected dimension $O(N)$. The columns $a_{vw}$ with $v\in R$, $w\in C$ are used only in the analysis: their input weights are $0$.
--
--   **Formalization Note.** $n_+$ is the published `RHLinalg.posIndex`. Over $\mathbb R$ the conjugate transpose is the transpose. A ring edge of the subtype $R$ is mapped to an edge slot of $V$ by `liftEdge`.
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, pp. 21–23, §6.1 (anchored template, Eq. (12), inputs, ratio 4n^5), §6.2 (A_C, A_{v,C}, anchor-goodness, k_v(C), K(C)), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Leverage
import Definitions.Def_WeightedSpectralSketch_LowerBound_Ring

open MeasureTheory Matrix
open scoped ENNReal

namespace WeightedSpectralSketch.LowerBound

/-- The slots of the anchored template (§6.1, p. 21): `ℓ b` anchor slots and `ℓ` ring blocks of
`b` slots each. An anchored labeling is a bijection `π : AnchSlot ℓ b ≃ V`, `|V| = 2 ℓ b`. -/
abbrev AnchSlot (ℓ b : ℕ) : Type := Fin (ℓ * b) ⊕ (Fin ℓ × Fin b)

/-- The anchor clique `C`: the vertices placed in anchor slots. The ring is `R = V \ C`. -/
noncomputable def anchorSet {ℓ b : ℕ} {V : Type*} [Fintype V] (π : AnchSlot ℓ b ≃ V) :
    Finset V :=
  open Classical in Finset.univ.filter fun v => (π.symm v).isLeft

/-- The base weight (12), p. 21, between two anchored slots: `w_int` between two anchor slots,
the ring weight (3) between two ring slots, and `0` between an anchor slot and a ring slot. -/
noncomputable def anchSlotWeight (ℓ b : ℕ) (wint : ℝ) : AnchSlot ℓ b → AnchSlot ℓ b → ℝ
  | .inl _, .inl _ => wint
  | .inr p, .inr p' => slotWeight ℓ b wint p p'
  | _, _ => 0

theorem anchSlotWeight_comm (ℓ b : ℕ) (wint : ℝ) (p p' : AnchSlot ℓ b) :
    anchSlotWeight ℓ b wint p p' = anchSlotWeight ℓ b wint p' p := by
  cases p <;> cases p' <;> simp [anchSlotWeight, slotWeight_comm]

/-- The anchored base weight `w_e` (12), p. 21, under the labeling `π`, with `w_int = n²`,
`n = 2 ℓ b`, and `w_ext = ℓ / (16 b²)`. Edges between the anchor and the ring have weight `0`. -/
noncomputable def anchBaseWeight (ℓ b : ℕ) {V : Type*} (π : AnchSlot ℓ b ≃ V) (e : EdgeSlot V) :
    ℝ :=
  Sym2.lift ⟨anchSlotWeight ℓ b (((2 * ℓ * b : ℕ) : ℝ) ^ 2),
    anchSlotWeight_comm ℓ b (((2 * ℓ * b : ℕ) : ℝ) ^ 2)⟩ (e.1.map π.symm)

/-- The anchored query edge `q = xy`, `x` in ring slot `(0, jx)` and `y` in ring slot
`(ℓ/2, jy)`. -/
def anchQuery {ℓ b : ℕ} [NeZero ℓ] {V : Type*} (π : AnchSlot ℓ b ≃ V) (jx jy : Fin b) : Sym2 V :=
  s(π (.inr (0, jx)), π (.inr (halfBlock ℓ, jy)))

/-- The anchored input weights (p. 21–22): `w̃_e = w_e z_e` (No) or `w_e z_e + 1{e = q}` (Yes);
coordinates outside the positive support of (12) are `0` in both cases. -/
noncomputable def anchInput (ℓ b : ℕ) [NeZero ℓ] {V : Type*} (jx jy : Fin b)
    (π : AnchSlot ℓ b ≃ V) (yes : Bool) (z : EdgeSlot V → ℝ) : EdgeSlot V → ℝ :=
  open Classical in fun e =>
    anchBaseWeight ℓ b π e * z e + if yes = true ∧ e.1 = anchQuery π jx jy then 1 else 0

/-- The support of the union of the two anchored distributions: every `anchInput π yes z` with
noise values `z_e ∈ [½, 3/2]`. -/
def anchSupport (ℓ b : ℕ) [NeZero ℓ] (V : Type*) [Fintype V] [DecidableEq V] (jx jy : Fin b) :
    Set (EdgeSlot V → ℝ) :=
  {w | ∃ (π : AnchSlot ℓ b ≃ V) (yes : Bool) (z : EdgeSlot V → ℝ),
    (∀ e, z e ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) ∧ w = anchInput ℓ b jx jy π yes z}

/-- The edge slots inside the anchor `C`, indexing the anchor columns `A_C` (p. 22). -/
abbrev anchorEdges {V : Type*} (C : Finset V) : Type _ := {e : EdgeSlot V // ∀ u ∈ e.1, u ∈ C}

/-- The matrix `A_C = [a_e : e ∈ binom(C, 2)]` of anchor columns. -/
def anchorMat {V : Type*} {N : ℕ} (A : Matrix (Fin N) (EdgeSlot V) ℝ) (C : Finset V) :
    Matrix (Fin N) (anchorEdges C) ℝ :=
  Matrix.of fun r e => A r e.1

/-- The star matrix `A_{v,C} = [a_{vw} : w ∈ C]` (p. 22); for `v ∉ C` each `vw` is an edge slot
(whose input weight is zero in the anchored distributions). -/
noncomputable def starMat {V : Type*} {N : ℕ} (A : Matrix (Fin N) (EdgeSlot V) ℝ) (C : Finset V)
    (v : V) : Matrix (Fin N) C ℝ :=
  Matrix.of fun r w => colS A s(v, w.1) r

/-- The columns of `[A_{u,C} A_{v,C} A_C]` for the pair `e = uv`: the endpoint-to-anchor columns
`a_{pw}` (`p ∈ e`, `w ∈ C`) followed by the anchor columns. -/
noncomputable def endpointCols {V : Type*} [DecidableEq V] {N : ℕ}
    (A : Matrix (Fin N) (EdgeSlot V) ℝ) (C : Finset V) (e : Sym2 V) :
    ({p : V × C // p.1 ∈ e} ⊕ anchorEdges C) → Fin N → ℝ :=
  Sum.elim (fun p => colS A s(p.1.1, p.1.2.1)) (fun k => Aᵀ k.1)

/-- The pair `e = uv` is anchor-good (p. 22): `lev_{a_{uv}}([A_{u,C} A_{v,C} A_C]) ≤ 1`. -/
def AnchorGood {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}
    (A : Matrix (Fin N) (EdgeSlot V) ℝ) (C : Finset V) (e : Sym2 V) : Prop :=
  lev (endpointCols A C e) (colS A e) ≤ 1

/-- `k_v(C) = n₊(A_{v,C} A_{v,C}ᵀ - A_C A_Cᵀ)` (p. 23), the number of strictly positive
eigenvalues counted with multiplicity (over `ℝ`, `Mᴴ = Mᵀ`). -/
noncomputable def kDim {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ} (A : Matrix (Fin N) (EdgeSlot V) ℝ)
    (C : Finset V) (v : V) : ℕ :=
  RHLinalg.posIndex ((isHermitian_mul_conjTranspose_self (starMat A C v)).sub
    (isHermitian_mul_conjTranspose_self (anchorMat A C)))

/-- `K(C) = ∑_{v ∈ R} k_v(C)`, `R = V \ C` (p. 23). -/
noncomputable def KDim {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}
    (A : Matrix (Fin N) (EdgeSlot V) ℝ) (C : Finset V) : ℕ :=
  ∑ v ∈ Finset.univ.filter (· ∉ C), kDim A C v

/-- A ring edge slot `e ∈ binom(R, 2)`, `R = {v // v ∉ C}`, viewed as an edge slot of `V`. -/
def liftEdge {V : Type*} (C : Finset V) (e : EdgeSlot {v // v ∉ C}) : EdgeSlot V :=
  ⟨e.1.map Subtype.val, by
    rw [Sym2.isDiag_map Subtype.val_injective]
    exact e.2⟩

end WeightedSpectralSketch.LowerBound


