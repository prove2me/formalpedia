-- Prove2me | Definitions.Def_DetCCHard_Supplement_Ineq10
-- name    : DetCCHard_Supplement_Ineq10
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:55:28.535224+00:00
-- url     : https://prove2.me/theorems/1f8e8582-3e70-4ea6-97c6-aec43d6056eb
-- title:
--   Parameters of Definition 6.1, costs (1), the Lemma 6.6 bounds, hypotheses (H1)–(H3) and the inequalities (10)
-- statement:
--   With $s$ dyadic and $\rho = 2^{-L}$, Definition 6.1 sets $q_1 = s - 2$, $q_2 = s^2/\rho$, $w = s^8$, $Q = s^{24}$, $x = \rho^8$, $\eta = s^{-2}$, $\theta = (512Q)^{-1}$ and $\delta_U = \eta/(16w)$. With $d = D(R)$, display (1) sets
--   $$
--   H_1 = d + \log s, \quad H_2 = H_1 + \log q_2, \quad C = H_2 + \log s + 1, \quad x_{\mathrm{cap}} = 2s\rho.
--   $$
--   The **template-layer deletion bounds** are $\mathcal P(A; x, H_1)$, $\mathcal P(R_{\mathrm{temp}}; x, H_2)$ and $\mathcal P(N_{\mathrm{ref}}; x, C - 1)$. The **collision bound** says that in the interlace of $R$ on the Γ-list, the first $q_1$ positions together with any three distinct tail positions require at least $H_1 + 1$ bits whenever every one of these positions retains base row weight at least $x_{\mathrm{cap}}$ within its block and the retained list labels have weight greater than $1/2$. **Source hardness** with cost $C$ and tolerance $\eta$ means $D(N) = C$ and every restriction of $N$ retaining at least $1 - \eta$ of each input set's weight costs at least $C$.
--
--   The **inequalities (10)** of Lemma F.1 require, with $\delta_v = \gamma|E|/(2\Delta n)$, $\zeta = \gamma/24$, $E_{\mathrm{exc}} = 2e(\theta, \eta/2)$ and $C_{128} = (2^{14}/(\lambda - 1/2)^2)^{128}$, that each quantity is strictly below its allowance:
--   $$
--   s\eta < 2^{-16}\min\{1, \delta_v, \mu\zeta\},\ \ \tfrac{4s|E|}{q_2} < 1,\ \ s^2\rho < \tfrac14,\ \ \tfrac{s q_1}{q_2} < \tfrac{\zeta}{128},\ \ \max\{q_2x, sx, wx\} < 10^{-4},
--   $$
--   $$
--   \tfrac{w^2x}{\eta} < \tfrac{1}{32\lambda},\ \ w^2q_2x < 1,\ \ \tfrac{wq_2x}{\eta} < \tfrac{1}{128\mu},\ \ \tfrac{e(\theta/4)}{sq_2} < 1,\ \ \tfrac{C_{128}s^{-128}}{\theta} < \tfrac14,\ \ \tfrac{2sE_{\mathrm{exc}}}{\eta w} < \tfrac1{16}.
--   $$
--   Also defined: the explicit lists of Definition 8.3 (positive normalized, exactly 8192-wise independent with the prescribed marginals) and the three label sequences of $(H3)$.
--
--   These predicates are the hypotheses of Theorems 6.9 and 6.16 and the conclusions of the last sentence of Theorem 6.9.
--
--   **Formalization Note** $e(v) = e(v, 1)$ with the published $e(v, \tau)$; all quantities are real.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Definition 6.1, p.18; display (1), p.20; Lemma 6.6, p.23; §6.5, p.27; Lemma F.1 and displays (8), (10), p.67

import Mathlib
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_DeletionBounds
import Definitions.Def_DetCCHard_TupleList
import Definitions.Def_DetCCHard_epsVT
import Definitions.Def_DetCCHard_SrcGraph
import Definitions.Def_DetCCHard_Supplement_RawList
import Definitions.Def_DetCCHard_Supplement_SrcData

namespace DetCCHard.Supplement

open DetCCHard

/-- The **block threshold** `x = ρ⁸` for `ρ = 2^{-L}` (Gaspers–He–Mackenzie, arXiv:2508.05597, held
version sha256 ad552d13…a4a03, Definition 6.1, p.18). -/
noncomputable def xOf (L : ℕ) : ℝ := (1 / 2 ^ L) ^ 8

/-- `η = s^{-2}` (Definition 6.1, p.18): the fraction of each input set's weight whose deletion the
lower bound for `N` survives. -/
noncomputable def etaOf (s : ℕ) : ℝ := 1 / (s : ℝ) ^ 2

/-- `θ = (512 Q)^{-1}` with `Q = s^{24}` (Definition 6.1, p.18): the row-weight threshold of the
deletion bounds of `W`. -/
noncomputable def thetaOf (s : ℕ) : ℝ := 1 / (512 * (s : ℝ) ^ 24)

/-- `δ_U = η/(16 w)` with `w = s^8` (Definition 6.1, p.18). -/
noncomputable def deltaUOf (s : ℕ) : ℝ := etaOf s / (16 * (s : ℝ) ^ 8)

/-- `x_cap = 2 s ρ` with `ρ = 2^{-L}` (display (1), p.20). -/
noncomputable def xcapOf (s L : ℕ) : ℝ := 2 * (s : ℝ) * (1 / 2 ^ L)

/-- `H₁ = d + log s` (display (1), p.20). -/
def costH1 (d s : ℕ) : ℕ := d + Nat.log 2 s

/-- `H₂ = H₁ + log q₂` (display (1), p.20). -/
def costH2 (d s q : ℕ) : ℕ := costH1 d s + Nat.log 2 q

/-- `C = H₂ + log s + 1` (display (1), p.20). -/
def costC (d s q : ℕ) : ℕ := costH2 d s q + Nat.log 2 s + 1

/-- The **weighted moment constant** `C₁₂₈ = (2^{14}/(λ − 1/2)²)^{128}` (display (8), p.67). -/
noncomputable def C128 : ℝ := ((2 : ℝ) ^ 14 / ((lam : ℝ) - 1 / 2) ^ 2) ^ 128

/-- `E_exc = 2 e(θ, η/2)` (display (8), p.67, and p.28), with the published `eVT`. -/
noncomputable def EexcOf (s : ℕ) : ℝ := 2 * (eVT (thetaOf s) (etaOf s / 2) : ℝ)

/-- The **numerical inequalities (10)** of Lemma F.1 (p.67), for the recipe of Definition 6.1 with
`s`, `ρ = 2^{-L}`, `q₁ = s − 2`, `q₂ = s²/ρ`, `w = s⁸`, `x = ρ⁸`, `η = s^{-2}`, `θ = (512 s^{24})^{-1}`,
and the graph-promise constants `δ_v = γ|E|/(2Δn)`, `ζ = γ/24`, `λ = 255/256`, `µ = 1/256`: each
quantity of the first column of the table is **below** (strictly less than) its required
allowance:
`sη < 2^{-16} min{1, δ_v, µζ}`, `4s|E|/q₂ < 1`, `s²ρ < 1/4`, `s q₁/q₂ < ζ/128`,
`max{q₂x, sx, wx} < 10^{-4}`, `w²x/η < 1/(32λ)`, `w² q₂ x < 1`, `w q₂ x/η < 1/(128µ)`,
`e(θ/4)/(s q₂) < 1`, `C₁₂₈ s^{-128}/θ < 1/4`, `2 s E_exc/(η w) < 1/16`.

**Formalization Note** `e(v) = e(v, 1)` (p.26); all quantities are real numbers. -/
def Ineq10 (Δ : ℕ) (γ : ℚ) (G : SrcGraph) (s L : ℕ) : Prop :=
  let sR : ℝ := s
  let nR : ℝ := G.n
  let ER : ℝ := G.edges.length
  let q1R : ℝ := ((s - 2 : ℕ) : ℝ)
  let q2R : ℝ := sR ^ 2 * 2 ^ L
  let wR : ℝ := sR ^ 8
  let x : ℝ := xOf L
  let η : ℝ := etaOf s
  let θ : ℝ := thetaOf s
  let δv : ℝ := (γ : ℝ) * ER / (2 * Δ * nR)
  let ζ : ℝ := (γ : ℝ) / 24
  sR * η < (1 / 2 ^ 16) * min 1 (min δv ((mu : ℝ) * ζ)) ∧
  4 * sR * ER / q2R < 1 ∧
  sR ^ 2 * (1 / 2 ^ L) < 1 / 4 ∧
  sR * q1R / q2R < ζ / 128 ∧
  max (q2R * x) (max (sR * x) (wR * x)) < 1 / 10 ^ 4 ∧
  wR ^ 2 * x / η < 1 / (32 * (lam : ℝ)) ∧
  wR ^ 2 * q2R * x < 1 ∧
  wR * q2R * x / η < 1 / (128 * (mu : ℝ)) ∧
  (eVT (θ / 4) 1 : ℝ) / (sR * q2R) < 1 ∧
  C128 * (1 / sR ^ 128) / θ < 1 / 4 ∧
  2 * sR * EexcOf s / (η * wR) < 1 / 16

namespace SrcData

variable (D : SrcData)

/-- The **template-layer deletion bounds** of Lemma 6.6 (p.23), hypothesis `(H1)` of §6.5 (p.27):
`P(A; x, H₁)`, `P(R_temp; x, H₂)` and `P(N_ref; x, C − 1)` with `x = ρ⁸`, `ρ = 2^{-L}`, and `H₁`, `H₂`,
`C` of display (1) for `d = D(R)`. `A` has row weights the Γ-list weights and column weights those of
`J`; `R_temp` has row weights those of `S` and column weights those of `J₂`; `N_ref` has the
normalized `Ω` weights on its rows and the `K` weights on its columns. -/
def TemplateDeletionBounds (L : ℕ) : Prop :=
  DeletionBounds D.A D.TΓ.ν (jWt D.R D.s) (xOf L) (costH1 (Dcost D.R.entry) D.s) ∧
  DeletionBounds D.Rtemp D.TS.ν (j2Wt D.TΓ D.q) (xOf L) (costH2 (Dcost D.R.entry) D.s D.q) ∧
  DeletionBounds D.Nref D.NrefWt D.KWt (xOf L) ((costC (Dcost D.R.entry) D.s D.q : ℤ) - 1)

/-- The **collision bound** of Lemma 6.6 (p.23): in the interlace of `R` on the Γ-list, the first
`q₁` positions together with any three distinct tail positions require at least `H₁ + 1` bits
whenever every one of these positions retains base row weight at least `x_cap = 2sρ` within its
block and the retained set of list labels has weight greater than `1/2`.

**Formalization Note** The restriction keeps rows only in the blocks of the `q₁` template positions
and the three tail positions `P3`; retaining further rows can only raise the cost. -/
def CollisionBound (L : ℕ) : Prop :=
  ∀ P3 : Finset (Fin (D.s + 1)), P3.card = 3 →
    ∀ U : Set (GPos D.s × D.R.X),
      (∀ r ∈ U, (∃ i, r.1 = Sum.inl i) ∨ ∃ k ∈ P3, r.1 = Sum.inr k) →
      (∀ i : Fin (D.s - 2), xcapOf D.s L ≤ (wt D.R.μX {u | (Sum.inl i, u) ∈ U} : ℝ)) →
      (∀ k ∈ P3, xcapOf D.s L ≤ (wt D.R.μX {u | (Sum.inr k, u) ∈ U} : ℝ)) →
      ∀ K : Set D.TΓ.L, (1 / 2 : ℚ) < wt D.TΓ.ν K →
        costH1 (Dcost D.R.entry) D.s + 1 ≤ commCost (D.TΓ.interlace D.R.entry) U K

/-- **Hardness of the source matrix after deletion**, the conclusion of Theorem 6.9 (p.24) and
hypothesis `(H2)` of §6.5 (p.27): `D(N) = C`, and every restriction of `N` retaining at least
`1 − η` of each input set's total weight (rows of `N` with the weights `NWt`, columns with the
weights `KWt`) has cost at least `C`. -/
def SourceHard (C : ℕ) (η : ℝ) : Prop :=
  Dcost D.N = C ∧
    ∀ (U : Set D.NRow) (V : Set D.KRow), 1 - η ≤ (wt D.NWt U : ℝ) → 1 - η ≤ (wt D.KWt V : ℝ) →
      C ≤ commCost D.N U V

/-- The **explicit lists** of Definition 8.3 (p.35), without the specific choice of Lemma 7.1:
the Γ-list, the template list and the bin-tuple list have positive normalized weights and are
exactly 8192-wise independent with marginals `μY`, the `J` weights and the `J₂` weights. -/
def ExplicitLists : Prop :=
  IsWeight D.TΓ.ν ∧ ExactlyIndepW D.TΓ.ν D.TΓ.z 8192 D.R.μY ∧
  IsWeight D.TS.ν ∧ ExactlyIndepW D.TS.ν D.TS.z 8192 (jWt D.R D.s) ∧
  IsWeight D.TB.ν ∧ ExactlyIndepW D.TB.ν D.TB.z 8192 (j2Wt D.TΓ D.q)

/-- The **three label sequences of `(H3)`** (§6.5, p.27, and Definition 8.3, p.36): lists of
`w`-tuples of type/bin/item labels (marginal `typeWt`), of base labels (marginal `μX`) and of
template labels (marginal the `S` weights), each with positive normalized weights and exactly
8192-wise independent across the `w` copies. -/
def H3Lists {w : ℕ} (T1 : RawList D.TypeLab (Fin w)) (T2 : RawList D.R.X (Fin w))
    (T3 : RawList D.TS.L (Fin w)) : Prop :=
  IsWeight T1.ν ∧ ExactlyIndepW T1.ν T1.z 8192 D.typeWt ∧
  IsWeight T2.ν ∧ ExactlyIndepW T2.ν T2.z 8192 D.R.μX ∧
  IsWeight T3.ν ∧ ExactlyIndepW T3.ν T3.z 8192 D.TS.ν

end SrcData

end DetCCHard.Supplement


