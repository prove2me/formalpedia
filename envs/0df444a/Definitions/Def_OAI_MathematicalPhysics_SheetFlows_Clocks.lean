-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
-- name    : OAI_MathematicalPhysics_SheetFlows_Clocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T00:54:26.732407+00:00
-- url     : https://prove2.me/theorems/1d34a36f-f6c5-412f-b15a-664a6301911d
-- title:
--   Smooth clocks, scheduled time pulses and tensor-product shear velocities
-- statement:
--   Let $\psi$ be the standard smooth transition function: $\psi(s)=E(s)/(E(s)+E(1-s))$ with $E(s)=e^{-1/s}$ for $s>0$ and $E(s)=0$ otherwise, so $\psi$ is $C^\infty$, equal to $0$ on $(-\infty,0]$ and to $1$ on $[1,\infty)$. Write $\Pi_Tg(x)=\sum_{k\in\mathbb{Z}}g(x-Tk)$ for the $T$-periodization of $g:\mathbb{R}\to\mathbb{R}$. Points of $\mathbb{R}^3$ are $x=(x_0,x_1,x_2)$, $e_0,e_1,e_2$ is the standard basis, and $P_ix=x-x_ie_i$.
--
--   1. **Clock and local pulse.** For $a,b\in\mathbb{R}$,
--   $$
--   \theta_{a,b}(t)=\psi\Bigl(\frac{t-a}{b-a}\Bigr),\qquad \rho_{a,b}=\theta_{a,b}' .
--   $$
--   Both are $C^\infty$. If $a<b$, then $\theta_{a,b}(t)=0$ for $t\le a$ and $\theta_{a,b}(t)=1$ for $t\ge b$, and $\rho_{a,b}(t)=0$ for $t\le a$ and for $t\ge b$.
--   2. **Periodic pulse.** $\pi_{a,b}=\Pi_1\rho_{a,b}$. It is $1$-periodic; it is $C^\infty$ if $a<b$; and if $0\le a<b\le1$, then $\pi_{a,b}(t)=\rho_{a,b}(t)$ for all $t\in[0,1]$.
--   3. **Time slots.** For $m\ge1$ and $i\in\{0,\dots,m-1\}$,
--   $$
--   \ell_{m,i}=\frac14+\frac{i}{2m},\qquad r_{m,i}=\ell_{m,i}+\frac1{4m},\qquad \sigma_{m,i}=\pi_{\ell_{m,i},\,r_{m,i}},
--   $$
--   and $\frac14\le\ell_{m,i}<r_{m,i}\le\frac34$.
--   4. **Tensor velocities.** For functions $g_0,g_1,g_2:\mathbb{R}\to\mathbb{R}$ put $G(x)=\prod_{j=0}^{2}g_j(x_j)$, and for a direction $i\in\{0,1,2\}$ let $V_{i,g}(t,x)=G(x)\,e_i$ (independent of $t$). Then:
--      - if every $g_j$ is $C^\infty$, so is $G$;
--      - if every $g_j$ is $10$-periodic, then $V_{i,g}(t,x+10k)=V_{i,g}(t,x)$ for all $t\in\mathbb{R}$, $x\in\mathbb{R}^3$ and $k\in\mathbb{Z}^3$;
--      - $\int_{[0,10)^3}G(x)\,dx=\prod_{j=0}^{2}\int_{[0,10)}g_j(s)\,ds$;
--      - if $\int_{[0,10)}g_j(s)\,ds=0$ for some $j$, then $\int_{[0,10)^3}V_{i,g}(t,x)\,dx=0$ for every $t$;
--      - if $g_i\equiv1$, then $G(P_ix)=G(x)$ for all $x$, so $V_{i,g}$ is the axial field $(t,x)\mapsto G(P_ix)\,e_i$; if in addition every $g_j$ is $C^\infty$, then $\operatorname{div}V_{i,g}=0$ and $D_xV_{i,g}(t,x)[V_{i,g}(t,x)]=0$ at every $(t,x)$.
--
--   The clock $\theta_{a,b}$ switches smoothly from $0$ to $1$ during $[a,b]$, so its derivative $\rho_{a,b}$ is a smooth time pulse supported in $[a,b]$ with total integral $1$. The scheduled pulses $\sigma_{m,0},\dots,\sigma_{m,m-1}$ are $1$-periodic and switch on $m$ stationary velocity fields one after another in the disjoint, ordered slots $[\ell_{m,i},r_{m,i}]\subset[\frac14,\frac34]$ of every unit time interval, so the resulting velocity vanishes near every integer time. Tensor velocities with $g_i\equiv1$ are the explicit divergence-free shear fields with vanishing advection term from which the whole flow is assembled.
--
--   **Formalization Note** The objects are `pulseClock`, `localPulse` (defined with `deriv`), `periodicPulse`, `slotLeft`, `slotRight`, `scheduledPulse`, `tensorScalar` and `tensorVelocity`. The slot index ranges over `Fin m`, which forces $m\ge1$ whenever a slot exists. The product formula for the integral (`tensorScalar_integral`) carries no integrability hypothesis; it holds with Lean's convention that the integral of a non-integrable function is $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Clocks.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Clocks.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SolenoidalSheetPrograms mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles

namespace OAI

/-! SheetFlows clocks. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal
open Filter
open scoped Topology

def pulseClock (a b t : ℝ) : ℝ := Real.smoothTransition ((t - a) / (b - a))

def localPulse (a b : ℝ) : ℝ → ℝ := deriv (pulseClock a b)

def periodicPulse (a b : ℝ) : ℝ → ℝ := periodize 1 (localPulse a b)

theorem pulseClock_contDiff (a b : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (pulseClock a b) := by
  unfold pulseClock
  fun_prop

theorem pulseClock_zero {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    pulseClock a b t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr ht) (sub_pos.mpr hab).le)

theorem pulseClock_one {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    pulseClock a b t = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hab)).mpr
    (by linarith))

theorem localPulse_contDiff (a b : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (localPulse a b) :=
  (contDiff_infty_iff_deriv.mp (pulseClock_contDiff a b)).2

theorem localPulse_zero_left {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    localPulse a b t = 0 := by
  have hd := ((pulseClock_contDiff a b).differentiable (by simp) t).hasDerivAt
  have hz : HasDerivWithinAt (pulseClock a b) 0 (Set.Iic t) t := by
    apply (hasDerivWithinAt_const t (Set.Iic t) (0 : ℝ)).congr
    · intro s hs
      exact pulseClock_zero hab (hs.trans ht)
    · exact pulseClock_zero hab ht
  exact (hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic t)).symm.trans
    (hz.derivWithin (uniqueDiffWithinAt_Iic t))

theorem localPulse_zero_right {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    localPulse a b t = 0 := by
  have hd := ((pulseClock_contDiff a b).differentiable (by simp) t).hasDerivAt
  have hz : HasDerivWithinAt (pulseClock a b) 0 (Set.Ici t) t := by
    apply (hasDerivWithinAt_const t (Set.Ici t) (1 : ℝ)).congr
    · intro s hs
      exact pulseClock_one hab (ht.trans hs)
    · exact pulseClock_one hab ht
  exact (hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici t)).symm.trans
    (hz.derivWithin (uniqueDiffWithinAt_Ici t))

theorem periodicPulse_periodic (a b : ℝ) :
    Function.Periodic (periodicPulse a b) 1 := periodize_periodic _ _

theorem periodicPulse_contDiff {a b : ℝ} (hab : a < b) :
    ContDiff ℝ (⊤ : ℕ∞) (periodicPulse a b) := by
  apply periodize_contDiff (a := a) (b := b) (by norm_num)
  · intro t ht
    rcases ht with ht | ht
    · exact localPulse_zero_left hab ht.le
    · exact localPulse_zero_right hab ht.le
  · exact localPulse_contDiff a b

theorem periodicPulse_on_chart {a b t : ℝ} (hab : a < b)
    (ha : 0 ≤ a) (hb : b ≤ 1) (ht : t ∈ Set.Icc 0 1) :
    periodicPulse a b t = localPulse a b t := by
  apply periodize_on_chart (by norm_num) _ _ ht
  intro s hs
  rcases hs with hs | hs
  · exact localPulse_zero_left hab (hs.trans ha)
  · exact localPulse_zero_right hab (hb.trans hs)

def slotLeft (m : ℕ) (i : Fin m) : ℝ := 1/4 + (i : ℝ) / (2 * m)

def slotRight (m : ℕ) (i : Fin m) : ℝ := slotLeft m i + 1 / (4 * m)

def scheduledPulse (m : ℕ) (i : Fin m) : ℝ → ℝ :=
  periodicPulse (slotLeft m i) (slotRight m i)

theorem slot_bounds {m : ℕ} (i : Fin m) :
    (1/4 : ℝ) ≤ slotLeft m i ∧ slotLeft m i < slotRight m i ∧
      slotRight m i ≤ 3/4 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hi₀ : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
  have hi₁ : (i : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
  dsimp [slotLeft, slotRight]
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hi₀ (by positivity))
  constructor
  · exact lt_add_of_pos_right _ (by positivity)
  · field_simp
    nlinarith

def tensorScalar (g : Fin 3 → ℝ → ℝ) (x : Space) : ℝ := ∏ j, g j (x j)

def tensorVelocity (i : Fin 3) (g : Fin 3 → ℝ → ℝ) : Field :=
  fun _ x => tensorScalar g x • basis i

theorem tensorScalar_contDiff (g : Fin 3 → ℝ → ℝ)
    (hg : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j)) :
    ContDiff ℝ (⊤ : ℕ∞) (tensorScalar g) :=
  contDiff_prod (fun j _ => (hg j).comp (contDiff_apply ℝ ℝ j))

theorem tensorVelocity_spatially_periodic (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hg : ∀ j, Function.Periodic (g j) 10) : SpatiallyPeriodic (tensorVelocity i g) := by
  intro t x k
  dsimp [tensorVelocity, tensorScalar]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simpa only [Pi.add_apply, deck, mul_comm (10 : ℝ)] using (hg j).int_mul (k j) (x j)

theorem tensorScalar_integral (g : Fin 3 → ℝ → ℝ) :
    (∫ x in fundamentalCell, tensorScalar g x) =
      ∏ j, ∫ s in Set.Ico (0 : ℝ) 10, g j s := by
  change (∫ x, (∏ j, g j (x j)) ∂((Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict
    (Set.pi Set.univ fun _ => Set.Ico (0 : ℝ) 10))) = _
  rw [Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod _

theorem tensorVelocity_mean_zero (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (j : Fin 3) (hg : (∫ s in Set.Ico (0 : ℝ) 10, g j s) = 0) :
    MeanZero (tensorVelocity i g) := by
  intro t
  dsimp [tensorVelocity]
  rw [integral_smul_const, tensorScalar_integral]
  have h : (∏ k, ∫ s in Set.Ico (0 : ℝ) 10, g k s) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) hg
  rw [h, zero_smul]

theorem tensorScalar_eraseAxis (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hg : ∀ s, g i s = 1) (x : Space) :
    tensorScalar g (eraseAxis i x) = tensorScalar g x := by
  apply Finset.prod_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    rw [hg, hg]
  · simp [eraseAxis_apply, basis, Pi.single_eq_of_ne hji]

theorem tensorVelocity_eq_axial (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hg : ∀ s, g i s = 1) :
    tensorVelocity i g = axialField i (fun _ => tensorScalar g) := by
  funext t x
  change tensorScalar g x • basis i = tensorScalar g (eraseAxis i x) • basis i
  rw [tensorScalar_eraseAxis i g hg]

theorem tensorVelocity_divergence_free (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hsm : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j)) (hg : ∀ s, g i s = 1) :
    DivergenceFree (tensorVelocity i g) := by
  rw [tensorVelocity_eq_axial i g hg]
  exact axialField_divergence_free i _ (fun _ =>
    (tensorScalar_contDiff g hsm).differentiable (by simp))

theorem tensorVelocity_advection_zero (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hsm : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j)) (hg : ∀ s, g i s = 1) :
    ∀ t x, advection (tensorVelocity i g) t x = 0 := by
  rw [tensorVelocity_eq_axial i g hg]
  intro t x
  exact advection_axialField i _ t x
    ((tensorScalar_contDiff g hsm).differentiable (by simp) _)

end Solenoidal
end
end

end OAI


