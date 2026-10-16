-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetProfiles
-- name    : OAI_MathematicalPhysics_SheetFlows_JetProfiles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:12:47.601395+00:00
-- url     : https://prove2.me/theorems/5561f1ec-1a69-4f30-92ce-8031059bd9cf
-- title:
--   Jet-expression formulas for the plateau, clock and pulse profiles, and periodic jet presentations
-- statement:
--   **Notation.** Let $E(x)=e^{-1/x}$ for $x>0$ and $E(x)=0$ for $x\le0$, and let $\psi(x)=E(x)/(E(x)+E(1-x))$ be the standard smooth transition function ($0$ on $(-\infty,0]$, $1$ on $[1,\infty)$). *Jet expressions* are the formal terms built from rational constants $q$, the variable $x$, sums, products, affine substitutions $e\mapsto e(ax+b)$ with $a,b\in\mathbb{Q}$, flat jets $\Phi_p(x)=p(1/x)E(x)$ with $p\in\mathbb{Q}[X]$, and the reciprocal $\mathcal R(x)=(E(x)+E(1-x))^{-1}$; each evaluates to a function $\mathbb{R}\to\mathbb{R}$ and has a symbolic derivative $e'$ whose value is the derivative of the value of $e$. The profiles concerned are, for real parameters,
--   $$
--   \beta_{h,d}(s)=\psi\Bigl(\frac{2(s+h+d)}{d}\Bigr)\psi\Bigl(\frac{2(h+d-s)}{d}\Bigr),\quad \lambda_{h,d}(s)=s\,\beta_{h,d}(s),\quad \theta_{a,b}(t)=\psi\Bigl(\frac{t-a}{b-a}\Bigr),\quad \rho_{a,b}=\theta_{a,b}',
--   $$
--   the $10$-periodizations $C_{h,d,c}(s)=\sum_{k\in\mathbb{Z}}\beta_{h,d}(s-c-10k)$ and $D_{h,d,c}(s)=\sum_{k\in\mathbb{Z}}\lambda_{h,d}(s-c-10k)$, and the $1$-periodization $\pi_{a,b}(t)=\sum_{k\in\mathbb{Z}}\rho_{a,b}(t-k)$.
--
--   1. **Expressions for the profiles.** For rational $h,d,c,a,b$:
--      - $\mathsf{tr}=\Phi_1\cdot\mathcal R$ has value $\psi$;
--      - $\mathsf{cut}_{h,d}=\mathsf{tr}\bigl(\tfrac2d x+\tfrac{2(h+d)}d\bigr)\cdot\mathsf{tr}\bigl(-\tfrac2d x+\tfrac{2(h+d)}d\bigr)$ has value $\beta_{h,d}$;
--      - $\mathsf{lin}_{h,d}=x\cdot\mathsf{cut}_{h,d}$ has value $\lambda_{h,d}$;
--      - $\mathsf{cut}_{h,d}(x-c)$ and $\mathsf{lin}_{h,d}(x-c)$ have values $\beta_{h,d}(x-c)$ and $\lambda_{h,d}(x-c)$;
--      - $\mathsf{clock}_{a,b}=\mathsf{tr}\bigl(\tfrac1{b-a}x-\tfrac{a}{b-a}\bigr)$ has value $\theta_{a,b}$, and $\mathsf{pulse}_{a,b}=(\mathsf{clock}_{a,b})'$ has value $\rho_{a,b}$.
--
--      These value identities hold for all rational parameters.
--   2. **Periodic jets.** For $T\in\mathbb{Q}$ and $f:\mathbb{R}\to\mathbb{R}$, a periodic jet of period $T$ for $f$ consists of the facts that $T>0$, that $f$ is $C^\infty$ and that $f$ is $T$-periodic, together with a jet expression $e$ whose value agrees with $f$ on $[0,T]$. A rational constant $q$ has a periodic jet of every period $T>0$ (with expression $q$), and if $f$ and $g$ have periodic jets of the same period $T$ with expressions $e_1$ and $e_2$, then $f+g$ and $fg$ have periodic jets of period $T$ with expressions $e_1+e_2$ and $e_1e_2$.
--   3. **Profiles with periodic jets.**
--      - If $h,d,c\in\mathbb{Q}$ with $d>0$, $h+d\le c$ and $c+h+d\le10$, then $C_{h,d,c}$ has a periodic jet of period $10$ with expression $\mathsf{cut}_{h,d}(x-c)$, and $D_{h,d,c}$ has one with expression $\mathsf{lin}_{h,d}(x-c)$.
--      - If $a,b\in\mathbb{Q}$ with $0\le a<b\le1$, then $\pi_{a,b}$ has a periodic jet of period $1$ with expression $\mathsf{pulse}_{a,b}$.
--
--   A periodic jet replaces a smooth periodic function defined by an infinite sum with a finite symbolic formula with rational data, valid on one period. Since jet expressions can be differentiated symbolically, this is the bridge between the analytic profiles from which an explicit Navier–Stokes velocity field is built and the effective, algorithmic description of its forcing and of bounds on all its derivatives.
--
--   **Formalization Note** The expressions are `JetExpr.transition`, `JetExpr.cutoff`, `JetExpr.linearCutoff`, `JetExpr.shiftedC`, `JetExpr.shiftedD` (the shift is `affine 1 (-c)`), `JetExpr.clock` and `JetExpr.clockPulse`, with value lemmas `transition_eval`, `cutoff_eval`, `linearCutoff_eval`, `shiftedC_eval`, `shiftedD_eval`, `clock_eval` and `clockPulse_eval`. `PeriodicJet T f` is a structure carrying data (the expression), not merely a proposition; the constructions are `PeriodicJet.const`, `PeriodicJet.add`, `PeriodicJet.mul`, `Cprofile_jet`, `Dprofile_jet` and `periodicPulse_jet`. Lean's convention $x/0=0$ makes the value identities hold even for degenerate parameters such as $d=0$ or $a=b$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/JetProfiles.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/JetProfiles.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SolenoidalSheetPrograms mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ShearCore
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Routing
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_JetCalculus

namespace OAI

/-! SheetFlows jet profiles. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology Polynomial
namespace Solenoidal
namespace JetExpr

def transition : JetExpr := .mul (.flat 1) .reciprocal

@[simp] theorem transition_eval (x : ℝ) : transition.eval x = Real.smoothTransition x := by
  simp [transition, eval, flatJet, transitionReciprocal, Real.smoothTransition, div_eq_mul_inv]

def cutoff (h d : ℚ) : JetExpr :=
  .mul (.affine (2/d) (2*(h+d)/d) transition)
    (.affine (-2/d) (2*(h+d)/d) transition)

def linearCutoff (h d : ℚ) : JetExpr := .mul .id (cutoff h d)

@[simp] theorem cutoff_eval (h d : ℚ) (x : ℝ) :
    (cutoff h d).eval x = plateau h d x := by
  simp only [cutoff, eval, transition_eval, plateau, Rat.cast_div, Rat.cast_mul,
    Rat.cast_add, Rat.cast_neg, Rat.cast_ofNat]
  congr 2 <;> ring

@[simp] theorem linearCutoff_eval (h d : ℚ) (x : ℝ) :
    (linearCutoff h d).eval x = linearProfile h d x := by
  simp [linearCutoff, eval, linearProfile]

def shiftedC (h d c : ℚ) : JetExpr := .affine 1 (-c) (cutoff h d)
def shiftedD (h d c : ℚ) : JetExpr := .affine 1 (-c) (linearCutoff h d)

def clock (a b : ℚ) : JetExpr := .affine (1/(b-a)) (-a/(b-a)) transition

def clockPulse (a b : ℚ) : JetExpr := (clock a b).diff

@[simp] theorem shiftedC_eval (h d c : ℚ) (x : ℝ) :
    (shiftedC h d c).eval x = plateau h d (x-c) := by
  simp [shiftedC, eval, sub_eq_add_neg]

@[simp] theorem shiftedD_eval (h d c : ℚ) (x : ℝ) :
    (shiftedD h d c).eval x = linearProfile h d (x-c) := by
  simp [shiftedD, eval, sub_eq_add_neg]

@[simp] theorem clock_eval (a b : ℚ) (x : ℝ) :
    (clock a b).eval x = pulseClock a b x := by
  simp only [clock, eval, transition_eval, pulseClock, Rat.cast_div, Rat.cast_one,
    Rat.cast_neg, Rat.cast_sub]
  congr 1
  ring

@[simp] theorem clockPulse_eval (a b : ℚ) (x : ℝ) :
    (clockPulse a b).eval x = localPulse a b x := by
  rw [clockPulse, ((clock a b).diff_correct x).deriv.symm]
  congr 1
  ext t
  exact clock_eval a b t

end JetExpr

structure PeriodicJet (T : ℚ) (f : ℝ → ℝ) where
  positive : 0 < T
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  periodic : Function.Periodic f T
  expression : JetExpr
  on_chart : Set.EqOn f expression.eval (Set.Icc 0 T)

namespace PeriodicJet

variable {T : ℚ} {f : ℝ → ℝ}

def const (T : ℚ) (hT : 0 < T) (q : ℚ) : PeriodicJet T (fun _ => (q:ℝ)) where
  positive := hT
  smooth := contDiff_const
  periodic := fun _ => rfl
  expression := .const q
  on_chart := fun _ _ => rfl

def add {g : ℝ → ℝ} (p : PeriodicJet T f) (q : PeriodicJet T g) :
    PeriodicJet T (fun x => f x + g x) where
  positive := p.positive
  smooth := p.smooth.add q.smooth
  periodic := p.periodic.add q.periodic
  expression := .add p.expression q.expression
  on_chart := by intro x hx; simp only [JetExpr.eval, p.on_chart hx, q.on_chart hx]

def mul {g : ℝ → ℝ} (p : PeriodicJet T f) (q : PeriodicJet T g) :
    PeriodicJet T (fun x => f x * g x) where
  positive := p.positive
  smooth := p.smooth.mul q.smooth
  periodic := p.periodic.mul q.periodic
  expression := .mul p.expression q.expression
  on_chart := by intro x hx; simp only [JetExpr.eval, p.on_chart hx, q.on_chart hx]

end PeriodicJet

def Cprofile_jet (h d c : ℚ) (hd : 0 < d) (hl : h+d ≤ c) (hu : c+(h+d) ≤ 10) :
    PeriodicJet 10 (Cprofile h d c) where
  positive := by norm_num
  smooth := Cprofile_contDiff _ _ (by exact_mod_cast hd)
  periodic := Cprofile_periodic _ _ _
  expression := JetExpr.shiftedC h d c
  on_chart := by
    intro x hx
    rw [JetExpr.shiftedC_eval]
    apply periodize_on_chart (by norm_num) _ _ hx
    apply shifted_profile_zero_outside _ (fun s hs => plateau_zero (by exact_mod_cast hd) hs)
    · exact_mod_cast hl
    · exact_mod_cast hu

def Dprofile_jet (h d c : ℚ) (hd : 0 < d) (hl : h+d ≤ c) (hu : c+(h+d) ≤ 10) :
    PeriodicJet 10 (Dprofile h d c) where
  positive := by norm_num
  smooth := Dprofile_contDiff _ _ (by exact_mod_cast hd)
  periodic := Dprofile_periodic _ _ _
  expression := JetExpr.shiftedD h d c
  on_chart := by
    intro x hx
    rw [JetExpr.shiftedD_eval]
    apply periodize_on_chart (by norm_num) _ _ hx
    apply shifted_profile_zero_outside _ (fun s hs => linearProfile_zero (by exact_mod_cast hd) hs)
    · exact_mod_cast hl
    · exact_mod_cast hu

def periodicPulse_jet (a b : ℚ) (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ 1) :
    PeriodicJet 1 (periodicPulse a b) where
  positive := by norm_num
  smooth := periodicPulse_contDiff (by exact_mod_cast hab)
  periodic := by simpa using periodicPulse_periodic (a:ℝ) (b:ℝ)
  expression := JetExpr.clockPulse a b
  on_chart := by
    intro x hx
    rw [JetExpr.clockPulse_eval]
    exact periodicPulse_on_chart (by exact_mod_cast hab) (by exact_mod_cast ha)
      (by exact_mod_cast hb) (by simpa using hx)

end Solenoidal
end

end OAI


