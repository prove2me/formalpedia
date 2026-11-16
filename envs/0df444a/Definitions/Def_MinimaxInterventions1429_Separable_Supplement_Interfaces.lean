-- Prove2me | Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Interfaces
-- name    : MinimaxInterventions1429_Separable_Supplement_Interfaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:11:42.412635+00:00
-- url     : https://prove2.me/theorems/defec846-2456-4c9a-85c8-d27ca2be6abc
-- title:
--   Response gaps, shared tolerance, and public control interfaces
-- statement:
--   Let $L,L'$ be real $m\times k$ tables, $\Delta_k$ the closed simplex, and $F_M(p)=\max_g\sum_hM_{gh}p_h$. The optimality gap and shared-response tolerance are
--   $$\operatorname{gap}_M(p)=F_M(p)-\min_{q\in\Delta_k}F_M(q),\qquad a_Q(L,L')=\sup_{B\in Q}\min_{p\in\Delta_k}\max\{\operatorname{gap}_{L+B}(p),\operatorname{gap}_{L'+B}(p)\}.$$
--   Here $Q$ is nonempty and bounded when used in a theorem. The joint diameter $J(L,L')$ takes the largest column range over all row contrasts of both tables. The separable subspace consists of $B_{gh}=b_g+c_h$; $S$ restricts its entry norm to $5$ and $S_U$ restricts a larger subspace $U$ to norm $16$. For a nonempty compact control set $K$ and a public norm bound $\tau$, put $D_\tau=1+2\tau$, $Q_K=\{C+D_\tau B:C\in K,B\in S\}$, and $\Xi(K)=\max_{C\in K}\Lambda(C)$.
--
--   Normalization and its inverse are literal affine maps. The two-run program tries the supplied maximizing control with sign plus, then minus, and stops at the first table. Failure is made total by returning zero. A canonical exact optimizer selects the minimum squared Euclidean norm point of the minimizing face; its existence, correctness, and measurability remain proof obligations. These objects supply interfaces and procedures, without assuming their guarantees.
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Sections 1.1, 3.4–3.5 and 5, printed pp.2–3, 13–14, 16–17 (PDF pp.4–5, 15–16, 18–19)

import Definitions.Def_MinimaxInterventions1429_Separable_ObservationLaws
set_option autoImplicit false

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement
open MeasureTheory

/-- Excess above the attained simplex minimum; dimensions are nonzero in all results. -/
def gap {m k : ℕ} (M : Table m k) (p : Mixture k) : ℝ :=
  objective M p - sInf (Set.range (objective M))

def jointDiameter {m k : ℕ} [NeZero k] (L L' : Table m k) : ℝ :=
  ⨆ h, max (⨆ g, contrasts L g h) (⨆ g, contrasts L' g h) -
    min (⨅ g, contrasts L g h) (⨅ g, contrasts L' g h)

def sharedTolerance {m k : ℕ} (Q : Set (Table m k)) (L L' : Table m k) : ℝ :=
  sSup {a | ∃ B ∈ Q, a = sInf (Set.range (fun p : Mixture k =>
    max (gap (L + B) p) (gap (L' + B) p)))}

def separableSpace (m k : ℕ) : Submodule ℝ (Table m k) where
  carrier := {B | IsSeparable B}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro A B ⟨a,c,ha⟩ ⟨b,d,hb⟩
    exact ⟨a+b,c+d,fun g h => by simp [ha g h,hb g h]; ring⟩
  smul_mem' := by
    rintro t B ⟨b,c,hb⟩
    exact ⟨t • b,t • c,fun g h => by simp [hb g h, mul_add]⟩

def enlargedQueries {m k : ℕ} (U : Submodule ℝ (Table m k)) : Set (Table m k) :=
  {B | B ∈ U ∧ entryNorm B ≤ 16}

def dilation (τ : ℝ) : ℝ := 1 + 2 * τ

def controlQueries {m k : ℕ} (K : Set (Table m k)) (τ : ℝ) : Set (Table m k) :=
  {Q | ∃ C ∈ K, ∃ B, Allowed B ∧ Q = C + dilation τ • B}

def availableInteraction {m k : ℕ} [NeZero k] (K : Set (Table m k)) : ℝ :=
  sSup (interaction '' K)

def ControlSet {m k : ℕ} (K : Set (Table m k)) (τ : ℝ) : Prop :=
  K.Nonempty ∧ IsCompact K ∧ 0 ≤ τ ∧ ∀ C ∈ K, entryNorm C ≤ τ

def symmetricControls {m k : ℕ} (K : Set (Table m k)) : Prop :=
  ∀ C, C ∈ K ↔ -C ∈ K

def normalized {m k : ℕ} (L C : Table m k) (τ : ℝ) : Table m k :=
  fun g h => (L g h + C g h + τ) / dilation τ

def unnormalize {m k : ℕ} (M C : Table m k) (τ : ℝ) : Table m k :=
  fun g h => dilation τ * M g h - C g h - τ

def segmentControl {m k : ℕ} (C : Table m k) : Set (Table m k) :=
  {Q | ∃ t : ℝ, |t| ≤ 1 ∧ Q = t • C}

def CommonResponse {m k : ℕ} (Q : Set (Table m k)) (L L' : Table m k) (α : ℝ) : Prop :=
  ∃ p : Table m k → Mixture k, ∀ B ∈ Q,
    Optimal (L + B) α (p B) ∧ Optimal (L' + B) α (p B)

def rowConstant {m k : ℕ} (a : Fin m → ℝ) : Table m k := fun g _ => a g

def shiftProgram {m k : ℕ} {A : Type} (C : Table m k) (τ : ℝ) :
    BitProgram m k A → BitProgram m k A
  | .done a => .done a
  | .ask q next => .ask ⟨C + dilation τ • q.surcharge, q.coordinate⟩
      (fun v => shiftProgram C τ (next v))

/-- Fixed sign order + then -, with early termination on the first returned table. -/
def twoShift {m k : ℕ} [NeZero m] [NeZero k]
    (C : Table m k) (τ α : ℝ) (T : ℕ) : BitProgram m k (Option (Table m k)) :=
  (shiftProgram C τ (reconstruction m k (α / dilation τ) T)).bind (fun out =>
    match out with
    | some (_,M) => .done (some (unnormalize M C τ))
    | none => (shiftProgram (-C) τ (reconstruction m k (α / dilation τ) T)).bind
        (fun out' => .done (out'.map (fun x => unnormalize x.2 (-C) τ))))

/-- Canonical selection: the unique smallest squared Euclidean norm exact minimizer.
Existence and measurability are theorem obligations, not assumed in this definition. -/
def selectMinimizer {m k : ℕ} [NeZero k] (M : Table m k) : Mixture k := by
  classical
  let p₀ : Mixture k := ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩
  exact if h : ∃ p : Mixture k, Optimal M 0 p ∧
    ∀ q : Mixture k, Optimal M 0 q → ∑ j, (p.val j)^2 ≤ ∑ j, (q.val j)^2
    then h.choose else p₀

/-- Replace every failure by the fixed zero table. -/
def totalShiftOutput {m k : ℕ} [NeZero m] [NeZero k] {S : Type*}
    (Dec : S → Table m k → Mixture k) (C : Table m k) (τ α : ℝ) (T : ℕ)
    (s : S) : Table m k :=
  ((twoShift C τ α T).run (thresholdOracle (Dec s)) []).1.getD 0

end MinimaxInterventions1429.Separable.Supplement


