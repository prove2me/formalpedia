-- Prove2me | Definitions.Def_SoarPolicy
-- name    : SoarPolicy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-22T18:56:21.759051+00:00
-- url     : https://prove2.me/theorems/613c2d36-14f3-4912-8b5f-ca61d85168bb
-- title:
--   The Simulate-Optimize-Assign-Repeat (SOAR) policy and its average match value
-- statement:
--   **Standing conventions.** Throughout, $\mathcal X$ (demand weight vectors) and $\mathcal Y$ (supply feature vectors) are measurable spaces, $P$ and $Q$ are probability measures on them, and the match quality function $\varphi : \mathcal X \times \mathcal Y \to \mathbb R$ is jointly measurable and bounded, $|\varphi(x,y)| \le C$ for all $x, y$. Expectations over $n$ i.i.d. demand units and $n$ independent i.i.d. supply units are integrals against the product measure $P^{\otimes n} \otimes Q^{\otimes n}$ on $\mathcal X^n \times \mathcal Y^n$. The hindsight optimum value is
--   $$U^H_n = \frac{1}{n}\,\mathbb E\Bigl[\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\sigma(t)}\bigr)\Bigr],$$
--   with $S_n$ the symmetric group, and the limiting hindsight optimum is $U_\infty = \sup_{n \ge 1} U^H_n$.
--
--   This module formalizes Algorithm 1, the SOAR policy, as a deterministic function of explicit random inputs, and its average expected match value $U_n(\mathrm{SOAR})$ as the expectation of that function.
--
--   **The offline solver.** SOAR relies on an offline assignment solver $\mathrm{opt}$ which, for every size $m$, every demand tuple $\hat x \in \mathcal X^m$ and every supply tuple $\tilde y \in \mathcal Y^m$, returns a permutation $\eta^\star = \mathrm{opt}(\hat x, \tilde y) \in S_m$ solving the maximum quality matching problem (equation (4)),
--   $$\sum_{k=1}^{m} \varphi\bigl(\hat x_k, \tilde y_{\eta(k)}\bigr) \le \sum_{k=1}^{m} \varphi\bigl(\hat x_k, \tilde y_{\eta^\star(k)}\bigr) \qquad \text{for every } \eta \in S_m .$$
--   Ties may be broken by any deterministic rule; the solver is required to be a measurable function of its inputs.
--
--   **One epoch.** Consider the epoch at which $k + 1$ supply units $\tilde y_0, \dots, \tilde y_k$ remain (relabelled in order). The epoch consumes three pieces of randomness: the arriving demand unit $X_t =: \hat x_0 \sim P$; the simulated future demand scenario $\hat x_1, \dots, \hat x_k$, i.i.d. $P$ (Algorithm 1, line 4); and a uniformly random permutation $\sigma$ of the $k + 1$ pool slots (line 5). These are independent, so the epoch randomness has law $P \otimes P^{\otimes k} \otimes \mathrm{Unif}(S_{k+1})$. The permuted pool places $\hat x_{\sigma(j)}$ in slot $j$. The solver is run on the permuted pool against the remaining supply, $\eta^\star = \mathrm{opt}\bigl((\hat x_{\sigma(j)})_{j}, \tilde y\bigr)$ (line 6). The arriving unit $\hat x_0$ occupies slot $\sigma^{-1}(0)$, so it is allocated the supply unit with index
--   $$i = \eta^\star\bigl(\sigma^{-1}(0)\bigr)$$
--   (line 7), and the supply units other than $\tilde y_i$ remain, relabelled in order as $\tilde y_0, \dots, \tilde y_{i-1}, \tilde y_{i+1}, \dots, \tilde y_k$ (lines 3 and 8).
--
--   **The full run.** With $n$ supply units, the epochs are run for $t = 1, \dots, n$; the epoch with $k + 1$ remaining units uses the randomness indexed by $k$ (it needs exactly $k$ simulated units), collects the match value $\varphi(X_t, Y_{\pi_t})$ of the current match, and continues with the relabelled remaining supply until none is left. The cumulative match value $\sum_{t=1}^{n} \varphi(X_t, Y_{\pi_t})$ collected by SOAR is thus a function of the initial supply tuple and of the randomness of the $n$ epochs. The law of all the randomness of a run is $Q^{\otimes n}$ for the supply, independently of the epoch randomness, each epoch drawing independently from its own law. The **average expected match value of SOAR** (equation (1)) is
--   $$U_n(\mathrm{SOAR}) = \frac{1}{n}\,\mathbb E\Bigl[\sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\pi^{\mathrm{SOAR}}_t}\bigr)\Bigr],$$
--   and its **regret** (equation (3)) is $\mathrm{Reg}_n(\mathrm{SOAR}) = U_\infty - U_n(\mathrm{SOAR})$.
--
--   **Role.** This is the object of the paper's main theorem. The construction records exactly the two features the proof of Theorem 1 relies on: the solver never learns which pool element is the true demand (the pool is randomly permuted before it is solved), and the remaining supply is carried forward as a tuple of the same kind, so that its distribution can be tracked epoch by epoch.
--
--   **Formalization Note** The paper's Algorithm 1 writes the allocated unit as $\tilde Y_{\eta^\star(\sigma(0))}$; since slot $j$ of the permuted pool holds $\hat X_{\sigma(j)}$, the arriving unit sits in slot $\sigma^{-1}(0)$ and the intended index is $\eta^\star(\sigma^{-1}(0))$, which is what is formalized (with the literal $\eta^\star(\sigma(0))$ the identity of Theorem 1 fails on small explicit instances). The uniform law on $S_{k+1}$ is the uniform probability mass function on a finite type, with the discrete $\sigma$-algebra. Simulation seeds are not modelled separately: the simulated units are drawn directly from $P$, and the solver's tie-breaking is an arbitrary deterministic measurable rule, which the paper states is sufficient for its results. The remaining supply is relabelled by the order-preserving bijection that skips the matched index; the paper's relabelling is unspecified, and any fixed relabelling yields the same law. The randomness of a run is a dependent product over the epoch index $k = 0, \dots, n-1$, epoch $k$ carrying $k$ simulated units; the epoch for the first arrival uses index $n - 1$. Dividing by $n$ is real division, so $U_0(\mathrm{SOAR}) = 0$ is a junk value; the cumulative value of a run with no supply is $0$.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 3.2.1 (Algorithm 1 and equation (4)) and Section 2 (equations (1) and (3))

import Mathlib
import Definitions.Def_SoarModel

/-!
# The Simulate-Optimize-Assign-Repeat (SOAR) policy

Chen, Kanoria, Kumar, Zhang, *Feature-Based Dynamic Matching*, Section 3.2, Algorithm 1.

An epoch in which `k + 1` supply units remain consumes three pieces of randomness: the arriving
demand unit, `k` simulated future demand units, and a uniformly random permutation of the
`k + 1`-element demand pool.  The pool is solved against the remaining supply by an offline
assignment solver, the arriving unit receives the supply unit its slot is assigned to, and the
remaining supply units are relabelled in order.
-/

open MeasureTheory
open scoped BigOperators

/-- The randomness consumed by one SOAR epoch in which `k + 1` supply units remain: the arriving
demand unit `X_t`, the `k` simulated demand units `X̂_1, …, X̂_k`, and the random permutation
`σ` of the `k + 1` pool slots. -/
abbrev SoarEpochRand (X : Type*) (k : ℕ) : Type _ :=
  X × (Fin k → X) × Equiv.Perm (Fin (k + 1))

/-- The uniform probability measure on a finite nonempty type. -/
noncomputable def SoarUniform (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] :
    Measure α :=
  (PMF.uniformOfFintype α).toMeasure

instance (α : Type*) [Fintype α] [Nonempty α] [MeasurableSpace α] :
    IsProbabilityMeasure (SoarUniform α) := by
  unfold SoarUniform; infer_instance

/-- The law of the randomness of one epoch with `k + 1` remaining supply units: the arriving
demand and the `k` simulated demand units are i.i.d. `P`, the permutation is uniform, and all are
independent. -/
noncomputable def SoarEpochMeasure {X : Type*} [MeasurableSpace X] (P : Measure X)
    [SigmaFinite P] (k : ℕ) : Measure (SoarEpochRand X k) :=
  P.prod ((Measure.pi fun _ : Fin k => P).prod (SoarUniform (Equiv.Perm (Fin (k + 1)))))

instance {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] (k : ℕ) :
    IsProbabilityMeasure (SoarEpochMeasure P k) := by
  unfold SoarEpochMeasure; infer_instance

/-- The permuted demand pool of an epoch: slot `j` holds `X̂_{σ(j)}`, where `X̂_0 = X_t` is the
arriving demand unit and `X̂_1, …, X̂_k` are the simulated units (Algorithm 1, line 5). -/
def SoarPool {X : Type*} {k : ℕ} (r : SoarEpochRand X k) : Fin (k + 1) → X :=
  fun j => Fin.cons (α := fun _ => X) r.1 r.2.1 (r.2.2 j)

/-- `opt` is an offline assignment solver for `φ`: for every size `m`, demand tuple and supply
tuple it returns a perfect assignment of maximum total quality (Algorithm 1, line 6, eq. (4)),
with an arbitrary deterministic tie-breaking rule. -/
def SoarIsSolver {X Y : Type*} (φ : X → Y → ℝ)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m)) : Prop :=
  ∀ (m : ℕ) (x : Fin m → X) (y : Fin m → Y) (η : Equiv.Perm (Fin m)),
    ∑ t, φ (x t) (y (η t)) ≤ ∑ t, φ (x t) (y (opt m x y t))

/-- The solver is a measurable function of its inputs. -/
def SoarSolverMeasurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m)) : Prop :=
  ∀ m : ℕ, Measurable fun p : (Fin m → X) × (Fin m → Y) => opt m p.1 p.2

/-- The index of the remaining supply unit that SOAR allocates to the arriving demand unit: the
solver is run on the permuted pool against the remaining supply `ys`, and the arriving unit, which
sits in slot `σ⁻¹(0)`, receives the supply unit `η⋆(σ⁻¹(0))` (Algorithm 1, line 7). -/
def SoarPick {X Y : Type*} (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m))
    {k : ℕ} (ys : Fin (k + 1) → Y) (r : SoarEpochRand X k) : Fin (k + 1) :=
  opt (k + 1) (SoarPool r) ys (r.2.2.symm 0)

/-- The supply units that remain after unit `i` has been matched, relabelled in order
(Algorithm 1, lines 3 and 8). -/
def SoarRemaining {Y : Type*} {k : ℕ} (ys : Fin (k + 1) → Y) (i : Fin (k + 1)) : Fin k → Y :=
  fun j => ys (i.succAbove j)

/-- The cumulative match value `∑ₜ φ(Xₜ, Y_{πₜ})` collected by SOAR over a full horizon, as a
function of the initial supply units and of the randomness of every epoch: with `k + 1` supply
units remaining the epoch consumes the randomness at index `k` (it needs `k` simulated units),
collects the value of the current match, and continues with the relabelled remaining supply. -/
noncomputable def SoarTotal {X Y : Type*} (φ : X → Y → ℝ)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m)) :
    (n : ℕ) → (Fin n → Y) → ((j : Fin n) → SoarEpochRand X j) → ℝ
  | 0, _, _ => 0
  | k + 1, ys, ω =>
      φ (ω (Fin.last k)).1 (ys (SoarPick opt ys (ω (Fin.last k)))) +
        SoarTotal φ opt k (SoarRemaining ys (SoarPick opt ys (ω (Fin.last k))))
          (fun j => ω j.castSucc)

/-- The law of all the randomness of a SOAR run with `n` supply units: the supply units are
i.i.d. `Q`, and independently every epoch draws its own randomness from `SoarEpochMeasure`. -/
noncomputable def SoarMeasure {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [SigmaFinite Q] (n : ℕ) :
    Measure ((Fin n → Y) × ((j : Fin n) → SoarEpochRand X j)) :=
  (Measure.pi fun _ : Fin n => Q).prod (Measure.pi fun j : Fin n => SoarEpochMeasure P j)

/-- The average expected match value `U_n(SOAR; P, Q, φ)` of SOAR (eq. (1)). -/
noncomputable def SoarValue {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [SigmaFinite Q] (φ : X → Y → ℝ)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m)) (n : ℕ) : ℝ :=
  (∫ ω, SoarTotal φ opt n ω.1 ω.2 ∂SoarMeasure P Q n) / n

/-- The regret of SOAR, `Reg_n(SOAR) = U_∞ - U_n(SOAR)` (eq. (3)). -/
noncomputable def SoarRegret {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [IsProbabilityMeasure P] [SigmaFinite Q] (φ : X → Y → ℝ)
    (opt : (m : ℕ) → (Fin m → X) → (Fin m → Y) → Equiv.Perm (Fin m)) (n : ℕ) : ℝ :=
  SoarLimit P Q φ - SoarValue P Q φ opt n


