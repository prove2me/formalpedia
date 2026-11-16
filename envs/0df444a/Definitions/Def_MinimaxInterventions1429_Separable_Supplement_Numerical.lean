-- Prove2me | Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Numerical
-- name    : MinimaxInterventions1429_Separable_Supplement_Numerical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:14:14.511795+00:00
-- url     : https://prove2.me/theorems/fe92167e-3f12-4607-af2b-29600a39d5c0
-- title:
--   Complete-mixture query programs and the appendix reconstruction procedures
-- statement:
--   A finite adaptive numerical program asks a full table surcharge and receives a complete mixture; its query budget counts calls, with universal branching over every possible reply. Accuracy is required only on the realized transcript. The Appendix A algorithm runs the published coarse stage at
--   $$T_0=\lceil\log_2(2^{16}/\lambda_0)\rceil,$$
--   retains the estimated contrasts, first-anchor plan and table, and applies two explicit numerical probes to each tree comparison. It restores row orientation signs, recovers all edge contrasts, sums along the tree, and refines the root contrasts for $\lceil\log_2(1/\gamma)\rceil$ steps.
--
--   For the probes, clipped estimated row differences determine $\widehat d$, $t_0$ is the clipped coarse level difference, and $t_1=t_0\mp\widehat d/8$ points toward zero. The decoded values are $d=(t_1-t_0)/(x_1-x_0)$ and $\Delta=t_0+\widehat d/2-dx_0$. Division is total; the theorem proves its denominator nonzero on calibrated data.
--
--   The cellwise program first estimates contrasts from thresholded numerical responses, then asks the literal two-row surcharges of Theorem C.2 and sets $\widehat a_g=-4(p_1-p_2)$, $\widehat a_1=0$. Its output is $\widehat a_g+\widehat\omega_{gh}$. Every query choice uses only public data and observed responses. These definitions supply procedures, with no reconstruction or accuracy contract embedded in their data.
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Appendices A and C, printed pp.27–30 (PDF pp.29–32)

import Definitions.Def_MinimaxInterventions1429_Separable_Supplement_Groups
set_option autoImplicit false

noncomputable section

namespace MinimaxInterventions1429.Separable.Supplement

abbrev NumericalHistory (m k : ℕ) := List (Table m k × Mixture k)
abbrev NumericalOracle (m k : ℕ) := NumericalHistory m k → Table m k → Mixture k

/-- Finite adaptive programs with complete numerical mixtures as replies. -/
inductive NumericalProgram (m k : ℕ) (A : Type) where
  | done : A → NumericalProgram m k A
  | ask : Table m k → (Mixture k → NumericalProgram m k A) → NumericalProgram m k A

def NumericalProgram.bind {m k : ℕ} {A B : Type}
    (p : NumericalProgram m k A) (f : A → NumericalProgram m k B) : NumericalProgram m k B :=
  match p with
  | .done a => f a
  | .ask q next => .ask q (fun x => (next x).bind f)

def NumericalProgram.run {m k : ℕ} {A : Type} (O : NumericalOracle m k) :
    NumericalProgram m k A → NumericalHistory m k → A × NumericalHistory m k
  | .done a,hist => (a,hist)
  | .ask q next,hist => let p := O hist q; (next p).run O (hist ++ [(q,p)])

def NumericalProgram.usesAtMost {m k : ℕ} {A : Type} : ℕ → NumericalProgram m k A → Prop
  | _, .done _ => True
  | 0, .ask _ _ => False
  | n+1, .ask _ next => ∀ p, (next p).usesAtMost n

def NumericalProgram.queriesSatisfy {m k : ℕ} {A : Type}
    (P : Table m k → Prop) : NumericalProgram m k A → Prop
  | .done _ => True
  | .ask q next => P q ∧ ∀ p, (next p).queriesSatisfy P

def numericalAccurate {m k : ℕ} (L : Table m k) (α : ℝ)
    (hist : NumericalHistory m k) : Prop :=
  ∀ B p, (B,p) ∈ hist → Optimal (L+B) α p

def liftBits {m k : ℕ} {A : Type} : BitProgram m k A → NumericalProgram m k A
  | .done a => .done a
  | .ask q next => .ask q.surcharge (fun p =>
      liftBits (next (decide ((1 : ℝ)/2 ≤ p.val q.coordinate))))

def ceilLog2 (x : ℝ) : ℕ := ⌈Real.log x / Real.log 2⌉₊
def coarsePrecision (lam : ℝ) : ℕ := ceilLog2 ((2:ℝ)^16 / lam)

def probeU {m k : ℕ} (w : Table m k) (g : Fin m) (h h' : Fin k) : ℝ := clip (w g h - w g h')
def probeSeparation {m k : ℕ} (w : Table m k) (g r : Fin m) (h h' : Fin k) : ℝ :=
  probeU w g h h' - probeU w r h h'
def probeT0 {m k : ℕ} (M : Table m k) (g r : Fin m) (h' : Fin k) : ℝ := clip (M g h' - M r h')
def probeT1 {m k : ℕ} (M w : Table m k) (g r : Fin m) (h h' : Fin k) : ℝ :=
  let t := probeT0 M g r h'
  if 0 ≤ t then t - probeSeparation w g r h h' / 8 else t + probeSeparation w g r h h' / 8

def numericalProbe {m k : ℕ} (w : Table m k) (g r : Fin m) (h h' : Fin k) (t : ℝ) : Table m k :=
  fun s j =>
    (if s = g then -t - probeSeparation w g r h h' / 2 else if s = r then 0 else -4) +
    (if j = h' then 0 else if j = h then -(probeU w g h h' + probeU w r h h') / 2 else 3)

def decodeProbes {m k : ℕ} (M w : Table m k) (g r : Fin m) (h h' : Fin k) (x₀ x₁ : ℝ) : ℝ × ℝ :=
  let t₀ := probeT0 M g r h'
  let t₁ := probeT1 M w g r h h'
  let d := (t₁-t₀) / (x₁-x₀)
  (t₀ + probeSeparation w g r h h' / 2 - d*x₀,d)

def twoProbes {m k : ℕ} (M w : Table m k) (g r : Fin m) (h h' : Fin k) : NumericalProgram m k (ℝ × ℝ) :=
  .ask (numericalProbe w g r h h' (probeT0 M g r h')) (fun p₀ =>
    .ask (numericalProbe w g r h h' (probeT1 M w g r h h')) (fun p₁ =>
      .done (decodeProbes M w g r h h' (p₀.val h) (p₁.val h))))

def orientedProbes {m k : ℕ} (M w : Table m k) (g r : Fin m) (h h' : Fin k) : NumericalProgram m k (ℝ × ℝ) :=
  if 0 ≤ probeSeparation w g r h h' then twoProbes M w g r h h'
  else (twoProbes M w r g h h').bind (fun x => .done (-x.1,-x.2))

def refineColumns {m k : ℕ} [NeZero k] (M w : Table m k) (g r : Fin m) (he : Fin k) (de : ℝ) :
    List (Fin k) → (Fin k → ℝ) → NumericalProgram m k (Fin k → ℝ)
  | [],v => .done v
  | h::rest,v =>
    let h' := if |probeSeparation w g r h 0| ≥ |probeSeparation w g r h he| then 0 else he
    (orientedProbes M w g r h h').bind (fun x =>
      refineColumns M w g r he de rest (Function.update v h (x.2 + if h' = he then de else 0)))

def refineEdge {m k : ℕ} [NeZero k] (M w : Table m k) (g r : Fin m) :
    NumericalProgram m k (ℝ × (Fin k → ℝ)) :=
  let he := firstMax (fun h => |w g h - w r h|)
  (orientedProbes M w g r he 0).bind (fun x =>
    (refineColumns M w g r he x.2
      ((List.finRange k).filter (fun h => h != 0 && h != he))
      (Function.update 0 he x.2)).bind (fun v => .done (x.1,v)))

def refineTree {m k : ℕ} [NeZero k] (M w : Table m k) (plan : AnchorPlan m) :
    List (Fin m) → (Fin m → ℝ) → Table m k → NumericalProgram m k ((Fin m → ℝ) × Table m k)
  | [],a,c => .done (a,c)
  | g::rest,a,c =>
    let r := plan.parent g
    (refineEdge M w g r).bind (fun x =>
      refineTree M w plan rest (Function.update a g (a r + x.1))
        (Function.update c g (fun h => c r h + x.2 h)))

def rootContrasts {m k : ℕ} [NeZero k] (g : Fin m) (T : ℕ) :
    List (Fin k) → (Fin k → ℝ) → NumericalProgram m k (Fin k → ℝ)
  | [],v => .done v
  | h::rest,v => (liftBits (contrastSearch 0 T g h)).bind (fun x =>
      rootContrasts g T rest (Function.update v h x))

/-- Coarse stage retains its observed contrasts, plan, and anchored table. -/
def coarseStage (m k : ℕ) [NeZero m] [NeZero k] (lam : ℝ) :
    NumericalProgram m k (Option (Table m k × AnchorPlan m × Table m k)) :=
  let T := coarsePrecision lam
  (liftBits (contrastPhase m k 0 T)).bind (fun w =>
    match planAnchors 0 T w with
    | none => .done none
    | some plan => (liftBits (estimateLevels 0 T w plan (alignmentOrder plan) 0)).bind
        (fun out => .done (out.map (fun x => (w,plan,x.2)))))

def exactNumerical (m k : ℕ) [NeZero m] [NeZero k] (lam γ : ℝ) : NumericalProgram m k (Option (Table m k)) :=
  (coarseStage m k lam).bind (fun out => match out with
    | none => .done none
    | some (w,plan,M) =>
      (refineTree M w plan (alignmentOrder plan) 0 0).bind (fun ac =>
        (rootContrasts plan.root (ceilLog2 (1/γ)) ((List.finRange k).filter (fun h => h != 0)) 0).bind
          (fun v => .done (some (fun g h => ac.1 g + ac.2 g h + v h)))))

def exactQueryBudget (m k : ℕ) (lam γ : ℝ) : ℕ :=
  (m*k-1)*coarsePrecision lam + 2*(m-1)*(k-1) + (k-1)*ceilLog2 (1/γ)

/-- Literal cellwise row-level query; source columns 1 and 2 are Lean 0 and 1. -/
def cellwiseQuery {m k : ℕ} [NeZero m] [NeZero k] (w : Table m k) (g : Fin m) : Table m k :=
  fun r h => if r = g then -w g h + (if h = 0 then 2 else if h.val = 1 then -2 else 4)
    else if r = 0 then -w 0 h + (if h = 0 then -2 else if h.val = 1 then 2 else 4)
    else -4

def cellwiseLevels {m k : ℕ} [NeZero m] [NeZero k] (w : Table m k) :
    List (Fin m) → (Fin m → ℝ) → NumericalProgram m k (Table m k)
  | [],a => .done (fun g h => a g + w g h)
  | g::rest,a => .ask (cellwiseQuery w g) (fun p =>
      let x₂ := ∑ h, if h.val = 1 then p.val h else 0
      cellwiseLevels w rest (Function.update a g (-4 * (p.val 0 - x₂))))

def cellwiseReconstruction (m k : ℕ) [NeZero m] [NeZero k] (α : ℝ) (T : ℕ) : NumericalProgram m k (Table m k) :=
  (liftBits (contrastPhase m k α T)).bind (fun w =>
    cellwiseLevels w ((List.finRange m).filter (fun g => g != 0)) 0)

def cellwiseOutput {m k : ℕ} [NeZero m] [NeZero k] {S : Type*}
    (Dec : S → Table m k → Mixture k) (α : ℝ) (T : ℕ) (s : S) : Table m k :=
  ((cellwiseReconstruction m k α T).run (fun _ B => Dec s B) []).1

end MinimaxInterventions1429.Separable.Supplement


