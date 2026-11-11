-- Prove2me | Definitions.Def_OrderSelProphet_Kernel_Model
-- name    : OrderSelProphet_Kernel_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:55:50.213665+00:00
-- url     : https://prove2.me/theorems/7e0d014f-5b65-4733-8edd-43c0d9831b01
-- title:
--   The order-selection model: loss scores, area curves (2), upper inverse, loads (6), arrival laws (5), allocations (4), the arrival-time algorithm, and the item-wise guarantee (1)
-- statement:
--   An **input** consists of $n\ge 1$ independent nonnegative real values $V_1,\dots,V_n$ with known laws $F_1,\dots,F_n$ (probability measures on $\mathbb R$ with $F_i((-\infty,0))=0$); it is **atomless** if no $F_i$ has an atom. Write $F_j(v)=P(V_j\le v)$.
--
--   - **Loss score** of item $i$: $U_i(v)=1-\prod_{j\ne i}F_j(v)$.
--   - **Area curve** (2): $A_i(x)=\mathbb E[(x-U_i)_+]$, and $\mu_i=A_i(1)$.
--   - **Upper generalized inverse**: $A^{\leftarrow}(b)=\sup\{x\in[0,1]:A(x)\le b\}$.
--   - **Lebesgue–Stieltjes measure** $df$ of a function nondecreasing on $[0,1]$: the Stieltjes measure of the right-continuous version of $f$ extended constantly outside $[0,1]$ (`lsMeasure`; $0$ if $f$ is not nondecreasing on $[0,1]$).
--   - **Threshold path** $y=A^{\leftarrow}\circ B$, **survival factor** $S_B(t)=\exp\!\big(-\Gamma\int_{(0,t]}dB(s)/(1-\Gamma s)\big)$, and with $S(t)=1-\Gamma t$ the **load** (6)
--   $$L_\Gamma(A,B)=\Gamma\int_{(0,1]}\frac{S_B(t)}{S(t)}\,dy(t)\in[0,\infty],$$
--   set to $\infty$ if $B$ or $y$ is not nondecreasing on $[0,1]$.
--   - **Arrival law** (5) on $(0,1]\cup\{\dagger\}$ ($\dagger$ is $\top$ in `WithTop ℝ`): density $\Gamma S_B/S$ with respect to $dy$ on $(0,1]$, plus mass $1-L_\Gamma(A,B)$ at $\dagger$.
--   - **Allocation functions** (4): $B_i(0)=0$, $B_i(1)=\mu_i$, $B_i$ nondecreasing on $[0,1]$, $\sum_iB_i(t)=t$ on $[0,1]$.
--   - **The algorithm**: items with $T_i\ne\dagger$ are inspected in increasing arrival time, ties by smaller index; the accepted item $I$ is the first inspected item that passes its own test $U_i(V_i)\le y_i(T_i)$, or none ($I=\dagger$, $\mathrm{ALG}=0$); otherwise $\mathrm{ALG}=V_I$.
--   - **Arrival run**: a probability space with $V_i\sim F_i$, $T_i\sim G_i$, all $2n$ variables mutually independent.
--   - **Item-wise guarantee** (1), integrated: $P(I=i,V_i\in E)=\Gamma\int_E\prod_{j\ne i}F_j\,dF_i$ for every Borel $E$.
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), §2, pp. 6–8, eqs. (1)–(6); Appendix A, p. 36

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-! # The order-selection model and the arrival-time algorithm

Peng and Tang, *Order-selection Prophet Inequality (Almost) Goes I.I.D.* (2026),
arXiv:2610.34892, §2, pp. 6–8, and Appendix A, p. 36.

An input is a finite family of laws `F i` (`i : Fin n`) of independent nonnegative real values.
Everything the algorithm is allowed to use is computed from these known laws; the realized
values enter only through the acceptance test of each item on its own value. -/

/-- An **input** (§2, p. 6): `n ≥ 1` items whose values have laws `F i` on `ℝ`, all supported on
`[0, ∞)` (nonnegative values). Each `F i` is also assumed to be a probability measure; that is a
separate instance hypothesis wherever an input is used. The paper assumes `n ≥ 2` ("the case
`n = 1` is immediate"); here `n ≥ 1`. -/
def IsInput {n : ℕ} (F : Fin n → Measure ℝ) : Prop :=
  0 < n ∧ ∀ i, F i (Iio 0) = 0

/-- An **atomless input** (§2, p. 6): an input whose value laws have no atoms. -/
def IsAtomlessInput {n : ℕ} (F : Fin n → Measure ℝ) : Prop :=
  IsInput F ∧ ∀ i (x : ℝ), F i {x} = 0

/-- The cumulative distribution function `F(x) = P(V ≤ x)` of a law on `ℝ`. -/
noncomputable def distFn (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (μ (Iic x)).toReal

/-- The **loss score** of item `i` at value `v` (§2.2, p. 7):
`U_i = 1 - ∏_{j ≠ i} F_j(v)`, the conditional probability that item `i` is not the maximum. -/
noncomputable def lossScore {n : ℕ} (F : Fin n → Measure ℝ) (i : Fin n) (v : ℝ) : ℝ :=
  1 - ∏ j ∈ Finset.univ.erase i, distFn (F j) v

/-- The **area curve** of item `i` (eq. (2), p. 7): `A_i(x) = E[(x - U_i)_+]`. -/
noncomputable def inputArea {n : ℕ} (F : Fin n → Measure ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  ∫ v, max (x - lossScore F i v) 0 ∂(F i)

/-- The **upper generalized inverse** (p. 7): `A^←(b) = sup {x ∈ [0,1] : A(x) ≤ b}`
(right-endpoint convention). -/
noncomputable def upperInv (A : ℝ → ℝ) (b : ℝ) : ℝ :=
  sSup {x ∈ Icc (0 : ℝ) 1 | A x ≤ b}

/-- The extension of `f` from `[0,1]` to `ℝ` that is constant on `(-∞, 0]` and on `[1, ∞)`. -/
noncomputable def unitExt (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (max 0 (min x 1))

theorem unitExt_monotone {f : ℝ → ℝ} (hf : MonotoneOn f (Icc 0 1)) : Monotone (unitExt f) := by
  intro a b hab
  have hmem : ∀ x : ℝ, max 0 (min x 1) ∈ Icc (0 : ℝ) 1 := fun x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  exact hf (hmem a) (hmem b) (max_le_max le_rfl (min_le_min_right _ hab))

/-- The **Lebesgue–Stieltjes measure** `df` of a function `f` that is nondecreasing on `[0,1]`
(§2.2, p. 8: "Integrals with respect to `B_i` and `y_i` are understood in the Lebesgue–Stieltjes
sense"). It is the Stieltjes measure of the right-continuous version of the extension `unitExt f`;
on `(0,1]` it gives `(s,t]` the mass `f(t+) - f(s+)`, which is `f t - f s` when `f` is continuous.
For a function that is not nondecreasing on `[0,1]` it is `0` (never used: see `loadL`). -/
noncomputable def lsMeasure (f : ℝ → ℝ) : Measure ℝ := by
  classical
  exact if hf : MonotoneOn f (Icc 0 1) then (unitExt_monotone hf).stieltjesFunction.measure else 0

/-- The **probability threshold path** `y = A^← ∘ B` (eq. (5), p. 8). -/
noncomputable def threshold (A B : ℝ → ℝ) (t : ℝ) : ℝ :=
  upperInv A (B t)

/-- The **survival factor** (eq. (5), p. 8):
`S_B(t) = exp(-Γ ∫_{(0,t]} dB(s) / (1 - Γ s))`. With `S(t) = 1 - Γ t`. -/
noncomputable def itemSurvival (Γ : ℝ) (B : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(Γ * ∫ s in Ioc 0 t, 1 / (1 - Γ * s) ∂(lsMeasure B)))

/-- The **arrival load** (eq. (6), p. 8):
`L_Γ(A, B) = Γ ∫_{(0,1]} S_B(t) / S(t) dy(t)` with `y = A^← ∘ B` and `S(t) = 1 - Γ t`,
a Lebesgue–Stieltjes integral, valued in `ℝ≥0∞`. If `B` or `y` is not nondecreasing on `[0,1]`
the Stieltjes integral is undefined and the load is set to `⊤` (infeasible); this never happens
for the allocations of the paper. -/
noncomputable def loadL (Γ : ℝ) (A B : ℝ → ℝ) : ℝ≥0∞ := by
  classical
  exact if MonotoneOn B (Icc 0 1) ∧ MonotoneOn (threshold A B) (Icc 0 1) then
    ENNReal.ofReal Γ * ∫⁻ t in Ioc 0 1, ENNReal.ofReal (itemSurvival Γ B t / (1 - Γ * t))
      ∂(lsMeasure (threshold A B))
  else ⊤

/-- The **arrival-time law** `G` on `(0,1] ∪ {†}` (eq. (5)–(6), p. 8), with `†` encoded as `⊤`
in `WithTop ℝ`: on `(0,1]` it has density `Γ S_B(t)/S(t)` with respect to `dy`, no arrival mass
is put at `t = 0`, and `†` gets the remaining mass `1 - L_Γ(A, B)`. It is a probability law
exactly when the load is at most one. -/
noncomputable def arrivalLaw (Γ : ℝ) (A B : ℝ → ℝ) : Measure (WithTop ℝ) :=
  Measure.map (fun t : ℝ => (t : WithTop ℝ))
      (((lsMeasure (threshold A B)).restrict (Ioc 0 1)).withDensity
        (fun t => ENNReal.ofReal (Γ * itemSurvival Γ B t / (1 - Γ * t))))
    + (1 - loadL Γ A B) • Measure.dirac ⊤

/-- **Allocation functions** (eq. (4), p. 7): `B_i(0) = 0`, `B_i(1) = μ_i := A_i(1)`, `B_i`
nondecreasing on `[0,1]`, and `∑_i B_i(t) = t` for every `t ∈ [0,1]`. -/
def IsAllocation {n : ℕ} (F : Fin n → Measure ℝ) (B : Fin n → ℝ → ℝ) : Prop :=
  (∀ i, B i 0 = 0 ∧ B i 1 = inputArea F i 1 ∧ MonotoneOn (B i) (Icc 0 1)) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, ∑ i, B i t = t

/-! ## The arrival-time algorithm (§2.1, p. 6; §2.2, p. 7) -/

/-- Item `i` is the **first item to pass**: it arrived (`T i ≠ †`), its own test passes, and every
other arrived item whose test passes comes strictly later, or at the same time with a larger
index (the fixed tie-breaking rule). Items are inspected in increasing order of arrival. -/
def IsFirstPass {n : ℕ} (T : Fin n → WithTop ℝ) (pass : Fin n → Prop) (i : Fin n) : Prop :=
  T i ≠ ⊤ ∧ pass i ∧ ∀ j, T j ≠ ⊤ → pass j → T i < T j ∨ (T i = T j ∧ i ≤ j)

/-- The **accepted item** `I` of the arrival-time algorithm: the first inspected item that passes
its own test, or `none` (the paper's `I = †`) if no item passes. The test `pass j` of item `j`
is evaluated on item `j`'s own data only (see `passTest`). -/
noncomputable def firstAccepted {n : ℕ} (T : Fin n → WithTop ℝ) (pass : Fin n → Prop) :
    Option (Fin n) := by
  classical
  exact if h : ∃ i, IsFirstPass T pass i then some (Classical.choose h) else none

/-- The acceptance test of the probability-scale algorithm (Step 3', p. 7) for item `i` with
arrival time `t` and value `v`: the item arrived at some time `s ∈ ℝ` and `U_i(v) ≤ y_i(s)`.
It reads only the item's own arrival time and value (and the known laws). -/
def passTest {n : ℕ} (F : Fin n → Measure ℝ) (y : ℝ → ℝ) (i : Fin n) (t : WithTop ℝ) (v : ℝ) :
    Prop :=
  ∃ s : ℝ, t = (s : WithTop ℝ) ∧ lossScore F i v ≤ y s

/-- The accepted index of the arrival-time algorithm with thresholds `y i` on input `F`, for
realized arrival times `T` and values `V`. -/
noncomputable def runIndex {n : ℕ} (F : Fin n → Measure ℝ) (y : Fin n → ℝ → ℝ)
    (T : Fin n → WithTop ℝ) (V : Fin n → ℝ) : Option (Fin n) :=
  firstAccepted T (fun i => passTest F (y i) i (T i) (V i))

/-- The value collected: `ALG = V_I`, and `ALG = 0` if no item is accepted (`I = †`). -/
def algValue {n : ℕ} (I : Option (Fin n)) (V : Fin n → ℝ) : ℝ :=
  match I with
  | none => 0
  | some i => V i

/-- A probability space carrying the **arrival-time algorithm** (§2.1 step 1): values `V i` with
laws `F i`, arrival times `T i ∈ WithTop ℝ` (`⊤ = †`) with laws `G i`, and the `2n` random
variables `V 1, …, V n, T 1, …, T n` mutually independent (arrival times independent of one
another and of the values). -/
def IsArrivalRun {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω) (V : Fin n → Ω → ℝ)
    (T : Fin n → Ω → WithTop ℝ) (F : Fin n → Measure ℝ) (G : Fin n → Measure (WithTop ℝ)) :
    Prop :=
  IsProbabilityMeasure P ∧ (∀ i, Measurable (V i)) ∧ (∀ i, Measurable (T i)) ∧
    (∀ i, P.map (V i) = F i) ∧ (∀ i, P.map (T i) = G i) ∧
    iIndep (fun k : Fin n ⊕ Fin n =>
      Sum.elim (fun i => MeasurableSpace.comap (V i) inferInstance)
        (fun i => MeasurableSpace.comap (T i) inferInstance) k) P

/-- The **exact item-wise guarantee** (1), p. 6, in integrated form: for every item `i` and every
Borel set `E`, `P(I = i, V_i ∈ E) = Γ ∫_E ∏_{j ≠ i} F_j(v) dF_i(v)`; equivalently
`P(I = i | V_i = v) = Γ ∏_{j ≠ i} F_j(v)` for `F_i`-almost every `v`. -/
def ItemwiseGuarantee {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (Γ : ℝ) (F : Fin n → Measure ℝ)
    (P : Measure Ω) (V : Fin n → Ω → ℝ) (I : Ω → Option (Fin n)) : Prop :=
  ∀ (i : Fin n) (E : Set ℝ), MeasurableSet E →
    P {ω | I ω = some i ∧ V i ω ∈ E} =
      ENNReal.ofReal Γ * ∫⁻ v in E, ENNReal.ofReal (∏ j ∈ Finset.univ.erase i, distFn (F j) v) ∂(F i)

end OrderSelProphet.Kernel


