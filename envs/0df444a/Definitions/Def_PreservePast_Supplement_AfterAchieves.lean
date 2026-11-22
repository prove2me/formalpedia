-- Prove2me | Definitions.Def_PreservePast_Supplement_AfterAchieves
-- name    : PreservePast_Supplement_AfterAchieves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:25:33.579812+00:00
-- url     : https://prove2.me/theorems/f687d817-7fb2-4591-91f6-9af113c6a172
-- title:
--   The association model of §3.2: histories, regret, legal updates, after- and before-query protocols, and the history classes of Theorems 5, 6, 10–12
-- statement:
--   There are $m$ outputs and $d+1$ inputs; the first input is the queried direction and the other $d$ are compensation directions. A **history** consists of an association matrix $A\in\mathbb R^{m\times d}$ with rows $a_i^\top$, a gradient block $F\in\mathbb R^{m\times d}$ and row metrics $Q_i\in\mathbb R^{d\times d}$ (in the baseline model $Q_i=I_d$). A unit query $p\in\mathbb R^m$ fixes the first column of the update $H=[p,-W]$, and the response-dependent old loss of the compensation block $W$ (rows $w_i^\top$) is
--   $$f_p(W)=\frac12\sum_i w_i^\top Q_i w_i-\langle F+\operatorname{diag}(p)A,\,W\rangle .$$
--   A block is **legal** if $\operatorname{rank}[p,W]\le r$ and $\|W\|_F\le\sqrt 8$ (equivalently $\|H\|_F\le 3$). The **regret** of $W$ is $f_p(W)-\min_{W'\text{ legal}}f_p(W')$.
--
--   A $B$-bit protocol **achieves regret $\varepsilon$ after the query** on a history class $\mathcal K$ and a query class $\mathcal Q$ if the encoder writes its message from the history and the public coins alone, and for every fixed history in $\mathcal K$ and query in $\mathcal Q$ the decoder's block is legal with regret at most $\varepsilon$ with probability at least $1-\delta$. It achieves it **before the query** if the encoder also sees $p$. The least widths are $B^{\mathrm{after}}_r(\varepsilon,\delta)$ and $B^{\mathrm{before}}_r(\varepsilon,\delta)$. A deterministic query-blind code succeeds with certainty for every query with the same message.
--
--   The classes used by the theorems are:
--
--   1. the **bounded-association class**: $\|a_i\|\le c$ for all $i$, $\|F\|_F\le\Gamma=3c/2$, $Q_i=I_d$;
--   2. the **paired class** (85): $m=2k$, $A=c[Z;-Z]$ for $Z\in\mathbb R^{k\times d}$ with unit rows, $\|F\|_F\le 3c/2$, $Q_i=I_d$, with the paired queries $p=2^{-1/2}[v;v]$, $v$ a unit vector of $\mathbb R^k$;
--   3. the bounded-association class with **at most $g$ distinct association rows**;
--   4. **private row metrics**: the bounds of 1 on $A$ and $F$, and symmetric $Q_i$ with $\|Q_i-I\|_{\mathrm{op}}\le\eta$;
--   5. **one shared covariance**: $Q_i=Q$ and $a_i=a$ for all $i$, with $q_-I\preceq Q\preceq q_+I$, $\|Q^{-1/2}a\|\le c$ and $\|FQ^{-1/2}\|_F\le 3c/2$.
--
--   The parameter $t=\min\{r-1,k,d\}$ is also defined here.
--
--   **Formalization Note** Outputs are indexed by an arbitrary finite type (the theorems use `Fin k ⊕ Fin k` for $m=2k$). The constant $\tfrac12$ of (17) and the coefficients $g_0$, $\alpha_i$ of the row covariances cancel from regret and are not part of the history. The comparator is an infimum over the legal set, which is nonempty and compact for $r\ge1$, so it is the minimum. Legality is part of the success event; requiring it on every outcome gives the same least width, since the decoder can replace an illegal block by $0$. Norm bounds are written squared, and $\|Q^{-1/2}a\|^2=a^\top Q^{-1}a$, $\|FQ^{-1/2}\|_F^2=\operatorname{tr}(FQ^{-1}F^\top)$.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), §3.2, pp.7–8 (PDF pp.9–10), eq. (17); Appendix D.2, p.28 (PDF p.30), eqs. (82)–(86); Appendix E, p.35 (PDF p.37), eq. (106); Appendix F, pp.39–41 (PDF pp.41–43), eqs. (120), (125)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2

open MeasureTheory Matrix

namespace PreservePast.Supplement

/-- **A history of the association model**: for outputs indexed by `ι` and `d` compensation
inputs, the association matrix `A` (rows `a_iᵀ`), the historical gradient block `F`, and the row
metrics `Q_i` of the free block. P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3.2, p.7 (PDF p.9): "Output i has conditional input
covariance Σ_i = [[1, a_iᵀ], [a_i, I_d]] with association vector ‖a_i‖ ≤ c < 1, stacked into
A ∈ ℝ^{m×d}, and historical gradient [0, F] with ‖F‖_F ≤ Γ = 3c/2. Both A and F are private
history"; Appendix F, p.39 (PDF p.41): "Row covariances Σ_i = [[α_i, a_iᵀ], [a_i, Q_i]] ≻ 0 and
gradient G = [g₀, F]".

**Formalization Note.** The coefficients `g₀` and `α_i` are not fields: "The remaining term
g₀ᵀp + ½ Σ_i α_i p_i² cancels from regret" (p.39), so they affect neither the regret nor the
legal set. The bounds defining a class (`‖a_i‖ ≤ c`, `‖F‖_F ≤ Γ`, the conditions on `Q_i`) are
stated by the class predicates below, not in the structure. -/
structure AssocHistory (ι : Type) (d : ℕ) where
  /-- The association matrix `A = [a_iᵀ]`. -/
  A : Matrix ι (Fin d) ℝ
  /-- The free block `F` of the historical gradient `[g₀, F]`. -/
  F : Matrix ι (Fin d) ℝ
  /-- The row metrics `Q_i` (`Q_i = I_d` in the baseline model of §3.2). -/
  Q : ι → Matrix (Fin d) (Fin d) ℝ

/-- The **response-dependent loss** (120), p.39 (PDF p.41):
`f_p(W) = ½ Σ_i w_iᵀ Q_i w_i − ⟨F + diag(p) A, W⟩`, `w_iᵀ` the rows of `W`. For `Q_i = I` this is
(17), p.7, `q_{A,F}([p, −W]) = ½ + ½‖W‖_F² − ⟨T_p, W⟩`, `T_p = F + diag(p)A`, minus the constant
`½`, which cancels from regret. -/
noncomputable def assocLoss {ι : Type} [Fintype ι] {d : ℕ} (h : AssocHistory ι d) (p : ι → ℝ)
    (W : Matrix ι (Fin d) ℝ) : ℝ :=
  (1 / 2) * ∑ i, (W i) ⬝ᵥ ((h.Q i) *ᵥ (W i)) - ∑ i, ∑ j, (h.F i j + p i * h.A i j) * W i j

/-- **Legal compensation blocks**: "Legal updates have rank[p, W] ≤ r and ‖W‖_F ≤ √8, equivalently
‖H‖_F ≤ 3" for `H = [p, −W]` (§3.2, p.7, PDF p.9). `‖W‖_F ≤ √8` is written `Σ W_ij² ≤ 8`. -/
def AssocLegal {ι : Type} [Fintype ι] {d : ℕ} (r : ℕ) (p : ι → ℝ) (W : Matrix ι (Fin d) ℝ) : Prop :=
  (Matrix.of fun (i : ι) (j : Unit ⊕ Fin d) => Sum.elim (fun _ => p i) (fun j => W i j) j).rank ≤ r ∧
    ∑ i, ∑ j, W i j ^ 2 ≤ 8

/-- The **regret** of a compensation block: its loss minus the minimum of the loss over the legal
set ("The full-history comparator minimizes this increment over the legal set", §3.2, p.7; (86),
p.28: `q_{Z,G}(H) − q*_r(v)`).

**Formalization Note.** The comparator is a real `⨅` over the subtype of legal blocks. The legal
set contains `W = 0` whenever `r ≥ 1` and is compact, and the loss is continuous, so the infimum
is the minimum of the source. -/
noncomputable def assocRegret {ι : Type} [Fintype ι] {d : ℕ} (h : AssocHistory ι d) (r : ℕ)
    (p : ι → ℝ) (W : Matrix ι (Fin d) ℝ) : ℝ :=
  assocLoss h p W - ⨅ W' : {W' : Matrix ι (Fin d) ℝ // AssocLegal r p W'}, assocLoss h p W'

/-- **The query is revealed after encoding** (the contract of `B_r^after(ε, δ)`). A `B`-bit
retained-state protocol for the history class `𝒦` and the query class `𝒬`: the encoder sees the
history and the public coins, the decoder sees the message, the coins and the query `p`, and for
every fixed history in `𝒦` and query in `𝒬` the output is legal with regret at most `ε` with
probability at least `1 − δ`. P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3.2, pp.7–8 (PDF pp.9–10): "Using the retained-state
convention of Section 1.2, require regret at most ε with probability at least 1 − δ. Denote the
minimum worst-case length by B_r^after"; (86), p.28 (PDF p.30).

**Formalization Note.** Legality is part of the success event. Requiring it on every outcome gives
the same minimum width, because the decoder knows `p` and `r` and can replace an illegal output
by the legal block `0`. Measurability as in the published `RandAchieves`. -/
def AfterAchieves {ι : Type} [Fintype ι] {d B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (𝒦 : Set (AssocHistory ι d)) (𝒬 : Set (ι → ℝ)) (r : ℕ) (ε δ : ℝ) (P : Measure Ω)
    (enc : AssocHistory ι d → Ω → Fin (2 ^ B))
    (dec : Fin (2 ^ B) → Ω → (ι → ℝ) → Matrix ι (Fin d) ℝ) : Prop :=
  IsProbabilityMeasure P ∧ (∀ h, Measurable (enc h)) ∧
    (∀ M p, Measurable (fun ω => Matrix.of.symm (dec M ω p))) ∧
    ∀ h ∈ 𝒦, ∀ p ∈ 𝒬, ENNReal.ofReal (1 - δ) ≤
      P {ω | AssocLegal r p (dec (enc h ω) ω p) ∧ assocRegret h r p (dec (enc h ω) ω p) ≤ ε}

/-- **The query is revealed before encoding** (the contract of `B_r^before(ε, δ)`): as
`AfterAchieves`, but the encoder also sees the query. §3.2, p.8 (PDF p.10): "and the cost when p
is revealed before encoding by B_r^before". -/
def BeforeAchieves {ι : Type} [Fintype ι] {d B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (𝒦 : Set (AssocHistory ι d)) (𝒬 : Set (ι → ℝ)) (r : ℕ) (ε δ : ℝ) (P : Measure Ω)
    (enc : AssocHistory ι d → (ι → ℝ) → Ω → Fin (2 ^ B))
    (dec : Fin (2 ^ B) → Ω → (ι → ℝ) → Matrix ι (Fin d) ℝ) : Prop :=
  IsProbabilityMeasure P ∧ (∀ h p, Measurable (enc h p)) ∧
    (∀ M p, Measurable (fun ω => Matrix.of.symm (dec M ω p))) ∧
    ∀ h ∈ 𝒦, ∀ p ∈ 𝒬, ENNReal.ofReal (1 - δ) ≤
      P {ω | AssocLegal r p (dec (enc h p ω) ω p) ∧ assocRegret h r p (dec (enc h p ω) ω p) ≤ ε}

/-- **A deterministic query-blind code succeeding for every query with the same message**
(Theorem 12, p.41: "The upper code is deterministic and succeeds for every query with the same
finite message"). -/
def DetAfterAchieves {ι : Type} [Fintype ι] {d B : ℕ}
    (𝒦 : Set (AssocHistory ι d)) (𝒬 : Set (ι → ℝ)) (r : ℕ) (ε : ℝ)
    (enc : AssocHistory ι d → Fin (2 ^ B))
    (dec : Fin (2 ^ B) → (ι → ℝ) → Matrix ι (Fin d) ℝ) : Prop :=
  ∀ h ∈ 𝒦, ∀ p ∈ 𝒬, AssocLegal r p (dec (enc h) p) ∧ assocRegret h r p (dec (enc h) p) ≤ ε

/-- The unit queries `p` (`Σ_i p_i² = 1`). -/
def unitQueries (ι : Type) [Fintype ι] : Set (ι → ℝ) := {p | ∑ i, p i ^ 2 = 1}

/-- **The bounded-association class** of §3.2, p.7 (PDF p.9): `‖a_i‖ ≤ c` for every row,
`‖F‖_F ≤ Γ = 3c/2`, isotropic row metrics `Q_i = I_d`. Norm bounds are written squared. -/
def boundedAssocClass (ι : Type) [Fintype ι] (d : ℕ) (c : ℝ) : Set (AssocHistory ι d) :=
  {h | (∀ i, ∑ j, h.A i j ^ 2 ≤ c ^ 2) ∧ ∑ i, ∑ j, h.F i j ^ 2 ≤ (3 * c / 2) ^ 2 ∧ ∀ i, h.Q i = 1}

/-- **The paired class** `𝓑_{c,Γ}` (85), p.28 (PDF p.30), embedded by (106), p.35 (PDF p.37):
outputs `Fin k ⊕ Fin k` (the rows `(i, +)` and `(i, −)`), associations `A = c[Z; −Z]` for a
`Z ∈ ℝ^{k×d}` with unit rows, `‖F‖_F ≤ Γ = 3c/2`, `Q_i = I_d` (and `g₀ = 0`, `ν_i = 1`, which do
not enter the regret). "The loss, comparator and legal set agree exactly" (p.35). -/
def pairedClass (k d : ℕ) (c : ℝ) : Set (AssocHistory (Fin k ⊕ Fin k) d) :=
  {h | (∃ Z : Matrix (Fin k) (Fin d) ℝ, (∀ i, ∑ j, Z i j ^ 2 = 1) ∧
        ∀ i j, h.A (Sum.inl i) j = c * Z i j ∧ h.A (Sum.inr i) j = -(c * Z i j)) ∧
      ∑ i, ∑ j, h.F i j ^ 2 ≤ (3 * c / 2) ^ 2 ∧ ∀ i, h.Q i = 1}

/-- **The paired queries** `p = Sv = 2^{-1/2}[v; v]` for a unit `v ∈ ℝᵏ` (§D.2, p.28;
(106), p.35). -/
def pairedQueries (k : ℕ) : Set (Fin k ⊕ Fin k → ℝ) :=
  {p | ∃ v : Fin k → ℝ, ∑ i, v i ^ 2 = 1 ∧
    ∀ i, p (Sum.inl i) = v i / Real.sqrt 2 ∧ p (Sum.inr i) = v i / Real.sqrt 2}

/-- The rank parameter `t = min{r − 1, k, d}` of Theorems 5, 6, 10–12 (used for `r ≥ 2`, where
the natural subtraction is exact). -/
def tParam (r k d : ℕ) : ℕ := min (r - 1) (min k d)

/-- **At most `g` distinct association rows** (Theorem 6, p.9, PDF p.11: "restrict the class to at
most g distinct association rows … and keep F arbitrary within its original bound"): the
bounded-association class whose matrix `A` has at most `g` distinct rows. Which outputs share a
row is private (Appendix E.5, "Private group labels"). -/
def sharedRowClass (ι : Type) [Fintype ι] (d : ℕ) (c : ℝ) (g : ℕ) : Set (AssocHistory ι d) :=
  {h | h ∈ boundedAssocClass ι d c ∧ (Set.range fun i => h.A i).ncard ≤ g}

/-- **Private row metrics near the identity** (Theorem 11, p.39, PDF p.41: "Under Theorem 5's
coefficient bounds …, allow arbitrary private Q_i with ‖Q_i − I‖_op ≤ η"): `‖a_i‖ ≤ c`,
`‖F‖_F ≤ 3c/2`, and symmetric `Q_i` within operator-norm distance `η` of `I_d`. -/
def metricAssocClass (ι : Type) [Fintype ι] (d : ℕ) (c η : ℝ) : Set (AssocHistory ι d) :=
  {h | (∀ i, ∑ j, h.A i j ^ 2 ≤ c ^ 2) ∧ ∑ i, ∑ j, h.F i j ^ 2 ≤ (3 * c / 2) ^ 2 ∧
    ∀ i, (h.Q i).IsSymm ∧ WainwrightHDS.NucNorm.opNorm2 (h.Q i - 1) ≤ η}

/-- **One unknown covariance shared by all outputs** (Theorem 12 and (125), p.41, PDF p.43;
§F.2: "Complete-output regression has one covariance Σ = [[α, aᵀ], [a, Q]]"): every row has the
same metric `Q` and the same association vector `a`, with `q₋ I ⪯ Q ⪯ q₊ I`, `‖Q^{-1/2}a‖ ≤ c`
and `‖F Q^{-1/2}‖_F ≤ Γ = 3c/2`. The last two are written `aᵀQ⁻¹a ≤ c²` and
`tr(F Q⁻¹ Fᵀ) ≤ Γ²`. Both `Q` and `a` are part of the private history. -/
def sharedCovClass (ι : Type) [Fintype ι] (d : ℕ) (c qlo qhi : ℝ) : Set (AssocHistory ι d) :=
  {h | ∃ (Q : Matrix (Fin d) (Fin d) ℝ) (a : Fin d → ℝ),
    (Q - qlo • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef ∧
    (qhi • (1 : Matrix (Fin d) (Fin d) ℝ) - Q).PosSemidef ∧
    a ⬝ᵥ (Q⁻¹ *ᵥ a) ≤ c ^ 2 ∧ Matrix.trace (h.F * Q⁻¹ * h.Fᵀ) ≤ (3 * c / 2) ^ 2 ∧
    ∀ i, h.Q i = Q ∧ ∀ j, h.A i j = a j}

end PreservePast.Supplement


