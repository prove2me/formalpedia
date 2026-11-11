-- Prove2me | Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_BalancedProduct
-- name    : FullRankSmallSetQLTC_IndependentChecks_BalancedProduct
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:48.855215+00:00
-- url     : https://prove2.me/theorems/21472760-62ae-424b-ac22-0461a11031ca
-- title:
--   The Lin–Hsieh balanced product code of two bipartite graphs
-- statement:
--   Let $\Gamma_A=(A_0,A_1,E_A)$ and $\Gamma_B=(B_0,B_1,E_B)$ be bipartite graphs with actions of one group $G$ on all four vertex classes. The **balanced product** has vertex blocks
--   $$V_{ij}=(A_i\times B_j)/G,\qquad i,j\in\{0,1\},$$
--   under the diagonal action $(v,w)\sim(gv,gw)$; its edges are quotiented by the same action. The **directional maps** are the adjacency maps of the quotient graphs (edge orbits counted modulo 2) obtained by stepping in one graph only:
--   $$S_j:\mathbb F_2^{V_{0j}}\to\mathbb F_2^{V_{1j}}\ (\text{a step in }\Gamma_A),\qquad T_i:\mathbb F_2^{V_{i0}}\to\mathbb F_2^{V_{i1}}\ (\text{a step in }\Gamma_B).$$
--   The CSS code (eq. (2.3)) has qubits $V_{10}\sqcup V_{01}$, X-checks $V_{00}$, Z-checks $V_{11}$, and
--   $$H_X=\delta_0^T=\begin{pmatrix}S_0^T&T_0^T\end{pmatrix},\qquad H_Z=\delta_1=\begin{pmatrix}T_1&S_1\end{pmatrix}.$$
--   For §5.3 the file also defines the weighted norm $|y|_w=|y_{10}|/D_1+|y_{01}|/D_2$ of $y=(y_{10},y_{01})$ and **local minimality**: adding any single row of a given check matrix to $y$ does not decrease a given weight.
--
--   **Formalization Note** Edges of $S_j$ are carried by triples $(a,a',b)$ with $a\sim a'$, edges of $T_i$ by triples $(a,b,b')$ with $b\sim b'$; each entry counts the $G$-orbits of such triples with the prescribed endpoint orbits, modulo $2$.
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), §2.1, pp. 10–11, eqs. (2.1)–(2.3); §5.3, p. 26 (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_Graph

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open MulAction Matrix

/-! # The Lin–Hsieh balanced product (§2.1, pp. 10–11)

`Γ_A = (A₀, A₁, E_A)` and `Γ_B = (B₀, B₁, E_B)` are bipartite graphs (`adjA : A₀ → A₁ → Prop`,
`adjB : B₀ → B₁ → Prop`) with actions of one group `G` on all four vertex classes. The vertex
blocks are `V_ij = (A_i × B_j)/G` under the diagonal action `(v, w) ∼ (gv, gw)`, and the edges are
quotiented by the same action. The directional maps are the adjacency maps (edge orbits counted
modulo 2) of the quotient graphs obtained by stepping in one graph only. -/

/-- The vertex block `(X × Y)/G` under the diagonal action. -/
abbrev BPVert (G X Y : Type*) [Group G] [MulAction G X] [MulAction G Y] :=
  orbitRel.Quotient G (X × Y)

section Maps

variable (G : Type*) [Group G] {A₀ A₁ B₀ B₁ : Type*}
  [MulAction G A₀] [MulAction G A₁] [MulAction G B₀] [MulAction G B₁]
  [Fintype A₀] [Fintype A₁] [Fintype B₀] [Fintype B₁]

/-- The directional map `S_j : 𝔽₂^{V_{0j}} → 𝔽₂^{V_{1j}}` (here `B = B_j`): the edges of the
balanced product are `((a, b), (a', b))` with `a ∼ a'` in `Γ_A`, carried by triples
`(a, a', b)`, quotiented by the diagonal action. -/
noncomputable def Smap (adjA : A₀ → A₁ → Prop) (B : Type*) [MulAction G B] [Fintype B] :
    Matrix (BPVert G A₁ B) (BPVert G A₀ B) (ZMod 2) :=
  edgeOrbitMatrix G (E := A₀ × A₁ × B) (fun e => adjA e.1 e.2.1)
    (fun e => (e.1, e.2.2)) (fun e => (e.2.1, e.2.2))

/-- The directional map `T_i : 𝔽₂^{V_{i0}} → 𝔽₂^{V_{i1}}` (here `A = A_i`): edges
`((a, b), (a, b'))` with `b ∼ b'` in `Γ_B`, carried by triples `(a, b, b')`. -/
noncomputable def Tmap (adjB : B₀ → B₁ → Prop) (A : Type*) [MulAction G A] [Fintype A] :
    Matrix (BPVert G A B₁) (BPVert G A B₀) (ZMod 2) :=
  edgeOrbitMatrix G (E := A × B₀ × B₁) (fun e => adjB e.2.1 e.2.2)
    (fun e => (e.1, e.2.1)) (fun e => (e.1, e.2.2))

/-- The qubits `V₁₀ ⊔ V₀₁` of the balanced-product code. -/
abbrev BPQubit := BPVert G A₁ B₀ ⊕ BPVert G A₀ B₁

/-- Eq. (2.3), p. 11: `H_X = δ₀ᵀ = (S₀ᵀ  T₀ᵀ)`, rows the X-checks `V₀₀`, columns the qubits
`V₁₀ ⊔ V₀₁`. -/
noncomputable def bpHX (adjA : A₀ → A₁ → Prop) (adjB : B₀ → B₁ → Prop) :
    Matrix (BPVert G A₀ B₀) (BPQubit G (A₀ := A₀) (A₁ := A₁) (B₀ := B₀) (B₁ := B₁)) (ZMod 2) :=
  Matrix.fromCols (Smap G adjA B₀)ᵀ (Tmap G adjB A₀)ᵀ

/-- Eq. (2.3), p. 11: `H_Z = δ₁ = (T₁  S₁)`, rows the Z-checks `V₁₁`, columns `V₁₀ ⊔ V₀₁`. -/
noncomputable def bpHZ (adjA : A₀ → A₁ → Prop) (adjB : B₀ → B₁ → Prop) :
    Matrix (BPVert G A₁ B₁) (BPQubit G (A₀ := A₀) (A₁ := A₁) (B₀ := B₀) (B₁ := B₁)) (ZMod 2) :=
  Matrix.fromCols (Tmap G adjB A₁) (Smap G adjA B₁)

end Maps

section Weights

variable {P Q : Type*} [Fintype P] [Fintype Q]

/-- The weighted norm `|y|_w = |y₁|/a + |y₂|/b` of a vector `y = (y₁, y₂)` on `P ⊔ Q`
(§5.3, p. 26, with `P = V₁₀`, `Q = V₀₁`, `a = D₁`, `b = D₂`). -/
noncomputable def blockWeight (a b : ℕ) (y : P ⊕ Q → ZMod 2) : ℝ :=
  (hammingNorm (fun v => y (Sum.inl v)) : ℝ) / a + (hammingNorm (fun v => y (Sum.inr v)) : ℝ) / b

/-- §5.3, p. 26: `y` is locally minimal for the weight `wt` with respect to the rows of `H`
if adding any single row of `H` to `y` does not decrease `wt`. -/
def IsLocallyMinimal {C Q' : Type*} (H : Matrix C Q' (ZMod 2)) (wt : (Q' → ZMod 2) → ℝ)
    (y : Q' → ZMod 2) : Prop :=
  ∀ i : C, wt y ≤ wt (y + H i)

end Weights

end FullRankSmallSetQLTC.IndependentChecks


