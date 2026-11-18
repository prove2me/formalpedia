-- Prove2me | Definitions.Def_IAFTRL_G26_body
-- name    : IAFTRL_G26_body
-- status  : Definition
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:27:49.420287+00:00
-- url     : https://prove2.me/theorems/556b9f5f-c2c5-4c7b-8bdd-b9bea405670e
-- title:
--   Abstract affine-field and scalar interfaces for the moment method of Appendix G (support maxima, freezing, integral moments)
-- statement:
--   This bundle collects the abstract objects of the moment method used for Lemma G.26.
--
--   **Geometry.** For $D\subseteq\mathbb R^d$ let $h_D(w)=\sup_{u\in D}u^\top w$ (`supp`). For an affine function $Z(u)=u^\top V+c$ set
--   $$
--   \max_D Z=h_D(V)+c\ (\texttt{posMax}),\qquad \max_D(-Z)=h_D(-V)-c\ (\texttt{negMax}),\qquad \max_D|Z|=\max\{\max_D Z,\max_D(-Z)\}\ (\texttt{absMax}).
--   $$
--   `rdim D` $=\dim\operatorname{vectorSpan}D$ is the affine dimension, and `nvol D` is the normalized relative volume (Hausdorff measure of dimension `rdim D`, conditioned on $D$).
--
--   **Field interface** (`FI`, Lemma G.25). For an adapted random affine field $Z_n(u)=u^\top V_n+c_n$ on a compact convex body $D$ with decreasing predictable alive events $J_n$, `FI D μ F T V c J β B lo hi m0` asserts measurability and boundedness, $N_n=\max_D(-Z_n)\ge0$, and for $m_0\le n<T$, a.s. on $J_n$, conditional drift of $\xi_n(u)=Z_{n+1}(u)-Z_n(u)$ in $[\mathrm{lo},\mathrm{hi}]$, $|\xi_n(u)|\le3\beta_n+(Z_n(u)+2N_n)/B$ and $\mathbb E[\xi_n(u)^2\mid\mathcal F_n]\le10\beta_n+2(Z_n(u)+2N_n)^2/(B(n+1))$, which are the budgets (G.153)–(G.154).
--
--   **Integral moments.** $G_n=\int_D Z_n^P\,d\sigma$ (`Gf`) and $F_n=\int_D(-Z_n)_+^P\,d\sigma$ (`Ff`), with the constants `Kabs`, `Cabs` of the absolute recurrence (G.488) and `Kneg`, `Hneg` of the negative recurrence (G.490).
--
--   **Freezing.** For predictable survival events $A_n$, $S_n=\bigcap_{i\le n}A_i$ (`survS`), and `frz X A` updates $X$ at round $n+1$ only on $S_n$. `crossA D V c J v λ s` $=J_s\cap\{s<v\ \text{or}\ N_s\le\lambda\}$ is the rule that freezes the field at its first crossing of level $\lambda$ after time $v$.
--
--   **Scalar interface** (`SI`, Lemma G.22). For a scalar process $Y_n$ with decreasing alive events $I_n$, `SI μ F Y I m N τ β B` asserts $Y_n\ge\tau_n>0$ on $I_n$, $|Y_{n+1}-Y_n|\le3Y_n/B$ and $\mathbb E[(Y_{n+1}-Y_n)^2\mid\mathcal F_n]\le10\beta_n+2Y_n^2/(B(n+1))$. Its killed moments are `kinv` $=\mathbb E[\mathbf 1_{I_n}Y_n^{-P}]$ and `kpos` $=\mathbb E[\mathbf 1_{I_n}Y_n^{P}]$.
--
--   These interfaces let the moment recurrences of Lemmas G.22–G.25 be proved once and then instantiated for the several run-level processes used in Lemmas G.26–G.30.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemmas G.22–G.25 (pp.165–172) and Lemma J.11 (p.211)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

-- ===== Solutions.G26.AbsAlg =====

/-! ### Pathwise algebra of the absolute integral moment recurrence (Lemma G.23) -/

namespace G26

/-- the inhomogeneous constant of the absolute recurrence -/
noncomputable def Kabs (P : ℕ) (b B : ℝ) : ℝ :=
  2 * P * (max 1 (2 * (P : ℝ))) ^ (P - 1) + b ^ P +
    10 * P ^ 2 * b * (max 1 (10 * (P : ℝ) ^ 2 * b)) ^ (P - 2) +
    P ^ 2 / 2 * (12 * P * b) ^ (P - 2) * (10 * b + 73728 * P ^ 2 * b ^ 2 / B)

end G26


-- ===== Solutions.G26.J11 =====

/-! ### Lemma J.11: uniform estimates for affine functions on a convex body -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace J11

variable {d : ℕ}

/-- the affine dimension of a set -/
noncomputable def rdim (D : Set (Fin d → ℝ)) : ℕ := Module.finrank ℝ (vectorSpan ℝ D)

/-- normalized relative volume on `D` -/
noncomputable def nvol (D : Set (Fin d → ℝ)) : Measure (Fin d → ℝ) :=
  (Measure.hausdorffMeasure (rdim D : ℝ))[|D]

section

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D) (hconv : Convex ℝ D) (hne : D.Nonempty)
include hD hconv hne

end

section Ineq

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D) (hconv : Convex ℝ D) (hne : D.Nonempty)
include hD hconv hne

end Ineq

end J11


-- ===== Solutions.G26.Supp =====

/-! ### Support functions and extrema of affine fields on a compact body -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ}

/-- the support function `h_D(w) = sup_{u ∈ D} u ⬝ᵥ w` -/
noncomputable def supp (D : Set (Fin d → ℝ)) (w : Fin d → ℝ) : ℝ :=
  sSup ((fun u => u ⬝ᵥ w) '' D)

/-- the negative maximum `max_D (−(u ⬝ᵥ V + c))` -/
noncomputable def negMax (D : Set (Fin d → ℝ)) (V : Fin d → ℝ) (c : ℝ) : ℝ := supp D (-V) - c

/-- the maximum `max_D (u ⬝ᵥ V + c)` -/
noncomputable def posMax (D : Set (Fin d → ℝ)) (V : Fin d → ℝ) (c : ℝ) : ℝ := supp D V + c

/-- the absolute maximum `max_D |u ⬝ᵥ V + c|` -/
noncomputable def absMax (D : Set (Fin d → ℝ)) (V : Fin d → ℝ) (c : ℝ) : ℝ :=
  max (posMax D V c) (negMax D V c)

section

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D)
include hD

end

end G26


-- ===== Solutions.G26.Iface =====

/-! ### The abstract affine-field interface of Lemma G.25 -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ} {Ω : Type*}

/-- the affine field `u ↦ u ⬝ᵥ V_n + c_n` -/
def fz (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (u : Fin d → ℝ) : ℝ :=
  u ⬝ᵥ V n ω + c n ω

/-- its increment -/
def fxi (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (u : Fin d → ℝ) : ℝ :=
  fz V c (n + 1) ω u - fz V c n ω u

/-- **The field interface.** On the alive sets `J n` (predictable, decreasing), the increments of
the affine field have conditional drift in `[lo, hi]`, magnitude at most
`3β_n + (Z_n(u) + 2N_n)/B` and conditional second moment at most
`10β_n + 2(Z_n(u) + 2N_n)²/(B(n+1))`, where `N_n` is the negative maximum. -/
structure FI (D : Set (Fin d → ℝ)) [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (F : ℕ → MeasurableSpace Ω) (T : ℕ) (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ)
    (J : ℕ → Set Ω) (β : ℕ → ℝ) (B lo hi : ℝ) (m0 : ℕ) : Prop where
  hD : IsCompact D
  hconv : Convex ℝ D
  hne : D.Nonempty
  Fle : ∀ n ≤ T, F n ≤ mΩ
  Fmono : ∀ n < T, F n ≤ F (n + 1)
  Vm : ∀ n ≤ T, Measurable[F n] (V n)
  cm : ∀ n ≤ T, Measurable[F n] (c n)
  Jm : ∀ n ≤ T, MeasurableSet[F n] (J n)
  Jmono : ∀ n, J (n + 1) ⊆ J n
  env : ∀ n ≤ T, ∃ r : ℝ, ∀ᵐ ω ∂μ, ∀ u ∈ D, |u ⬝ᵥ V n ω + c n ω| ≤ r
  N0 : ∀ n ≤ T, ∀ᵐ ω ∂μ, 0 ≤ negMax D (V n ω) (c n ω)
  drift : ∀ n, m0 ≤ n → n < T → ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J n →
    lo ≤ μ[fun ω => fxi V c n ω u | F n] ω ∧ μ[fun ω => fxi V c n ω u | F n] ω ≤ hi
  mag : ∀ n, m0 ≤ n → n < T → ∀ᵐ ω ∂μ, ω ∈ J n → ∀ u ∈ D,
    |fxi V c n ω u| ≤ 3 * β n + (fz V c n ω u + 2 * negMax D (V n ω) (c n ω)) / B
  sec : ∀ n, m0 ≤ n → n < T → ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J n →
    μ[fun ω => fxi V c n ω u ^ 2 | F n] ω ≤
      10 * β n + 2 * (fz V c n ω u + 2 * negMax D (V n ω) (c n ω)) ^ 2 / (B * ((n : ℝ) + 1))

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end

end G26


-- ===== Solutions.G26.AbsRec =====

/-! ### The absolute integral moment recurrence (Lemmas G.23, G.25) -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {d : ℕ} {Ω : Type*}

/-- the integral moment `G_n = ∫ Z_n^P dσ` -/
noncomputable def Gf (D : Set (Fin d → ℝ)) (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (P : ℕ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∫ u, fz V c n ω u ^ P ∂(nvol D)

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

/-- the constant of the absolute envelope -/
noncomputable def Cabs (P : ℕ) (b B C0 : ℝ) : ℝ :=
  max C0 (Kabs P b B / (P - (3 + 1152 * P ^ 2 / B)))

end G26


-- ===== Solutions.G26.Freeze =====

/-! ### Freezing an affine field at a predictable stopping rule -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ} {Ω : Type*}

/-- the surviving set `S_n = ⋂_{i ≤ n} A_i` -/
def survS (A : ℕ → Set Ω) (n : ℕ) : Set Ω := ⋂ i ∈ Finset.range (n + 1), A i

open Classical in
/-- the frozen field: updated at round `n` only on `S_n` -/
noncomputable def frz {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) : ℕ → Ω → E
  | 0 => X 0
  | n + 1 => fun ω => if ω ∈ survS A n then X (n + 1) ω else frz X A n ω

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end

end G26


-- ===== Solutions.G26.NegAlg =====

/-! ### Pathwise algebra of the negative integral moment recurrence (Lemma G.24) -/

namespace G26

/-- the inhomogeneous constant of the negative recurrence, `P = 4k` -/
noncomputable def Kneg (k : ℕ) (b B : ℝ) : ℝ :=
  (320 * (4 * k : ℝ) ^ 2) ^ (2 * k) * b ^ (2 * k) +
    (4 * k : ℝ) ^ 2 / 2 * (10 + 20000 * (4 * k : ℝ) ^ 2 / B) * (37 * (4 * k : ℝ)) ^ (4 * k - 2) *
      b ^ (4 * k)

end G26


-- ===== Solutions.G26.NegRec =====

/-! ### The negative integral moment recurrence (Lemmas G.24, G.25) -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {d : ℕ} {Ω : Type*}

/-- the negative integral moment `F_n = ∫ (−Z_n)₊^P dσ` -/
noncomputable def Ff (D : Set (Fin d → ℝ)) (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (P : ℕ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∫ u, (max (-fz V c n ω u) 0) ^ P ∂(nvol D)

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

/-- the particular-solution constant of the negative envelope -/
noncomputable def Hneg (k : ℕ) (b B : ℝ) : ℝ :=
  Kneg k b B / (3 * k - (1 + 1024 * (4 * k : ℝ) ^ 2 / B))

end G26


-- ===== Solutions.G26.Cross =====

/-! ### Block maxima of negative maxima by freezing at the first crossing -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

/-- the crossing rule: survive while alive and (before `v` or below the level) -/
def crossA (D : Set (Fin d → ℝ)) (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (J : ℕ → Set Ω)
    (v : ℕ) (lam : ℝ) (s : ℕ) : Set Ω :=
  J s ∩ {ω | s < v ∨ negMax D (V s ω) (c s ω) ≤ lam}

end G26


-- ===== Solutions.G26.Scalar =====

/-! ### Killed scalar local moments (Lemma G.22 and the local moments of Lemma G.28) -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {Ω : Type*}

/-- **The scalar interface.** On the alive sets `I n` (predictable, decreasing) the positive
variable `Y_n ≥ τ_n` moves by relative increments at most `3/B` with conditional second moment
at most `10 β_n + 2 Y_n²/(B(n+1))`. -/
structure SI [mΩ : MeasurableSpace Ω] (μ : Measure Ω) (F : ℕ → MeasurableSpace Ω)
    (Y : ℕ → Ω → ℝ) (I : ℕ → Set Ω) (m N : ℕ) (τ β : ℕ → ℝ) (B : ℝ) : Prop where
  Fle : ∀ n ≤ N, F n ≤ mΩ
  Ym : ∀ n ≤ N, Measurable[F n] (Y n)
  Im : ∀ n ≤ N, MeasurableSet[F n] (I n)
  Imono : ∀ n, I (n + 1) ⊆ I n
  τpos : ∀ n, 0 < τ n
  low : ∀ n, m ≤ n → n ≤ N → ∀ᵐ ω ∂μ, ω ∈ I n → τ n ≤ Y n ω
  env : ∀ n ≤ N, ∃ r : ℝ, ∀ᵐ ω ∂μ, |Y n ω| ≤ r
  mag : ∀ n, m ≤ n → n < N → ∀ᵐ ω ∂μ, ω ∈ I n → |Y (n + 1) ω - Y n ω| ≤ 3 * Y n ω / B
  sec : ∀ n, m ≤ n → n < N → ∀ᵐ ω ∂μ, ω ∈ I n →
    μ[fun ω => (Y (n + 1) ω - Y n ω) ^ 2 | F n] ω ≤ 10 * β n + 2 * Y n ω ^ 2 / (B * ((n : ℝ) + 1))

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

/-- the killed inverse moment `E[1_{I_n} Y_n^{-P}]` -/
noncomputable def kinv (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (I : ℕ → Set Ω) (P n : ℕ) : ℝ :=
  ∫ ω, (I n).indicator (fun ω => (Y n ω)⁻¹ ^ P) ω ∂μ

/-- the killed positive moment `E[1_{I_n} Y_n^P]` -/
noncomputable def kpos (μ : Measure Ω) (Y : ℕ → Ω → ℝ) (I : ℕ → Set Ω) (P n : ℕ) : ℝ :=
  ∫ ω, (I n).indicator (fun ω => Y n ω ^ P) ω ∂μ

end G26


