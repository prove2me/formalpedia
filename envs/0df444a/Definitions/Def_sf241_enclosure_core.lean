-- Prove2me | Definitions.Def_sf241_enclosure_core
-- name    : sf241_enclosure_core
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-05T02:14:24.983633+00:00
-- url     : https://prove2.me/theorems/702658c8-1027-4429-8e37-09122f36cecd
-- title:
--   Shooting at $\kappa=4$: enclosure infrastructure in $z=\tan(\theta/2)$
-- statement:
--   Infrastructure for a validated enclosure of shots of the profile equation (2.6) at $\kappa=4$.
--
--   **Substitution.** Put $z=\tan(\theta/2)$, $k(z)=h(\theta)$, $P(z)=\sin\theta\,h'(\theta)$. Then (2.6) becomes
--   $$k'=\frac{P}{z},\qquad P'=\frac{F(z,k)}{z},\qquad F=\tfrac12\sin 2k+2\sin^2\theta\,\big(\sin 2k\cos 2\theta-\cos 2k\sin 2\theta\big),$$
--   where $\sin^2\theta,\cos2\theta,\sin2\theta$ are rational functions of $z$, and $\theta=\pi/2$ is $z=1$. All coefficients are rational, so every bound below is checked in exact rational arithmetic.
--
--   Contents:
--
--   1. Rational polynomials, evaluation, shifting, and a bound $\sum|b_i|r^i$ on an interval.
--   2. One step on a piece $[z_l,z_r]$: polynomial approximations $G\approx k$, $Q\approx P$, $X\approx\cos 2k$, $Y\approx\sin 2k$ with polynomial defects; two Grönwall estimates (first for $(\cos 2G,\sin 2G)$, then for $(k,P)$) turn error bounds $(e,E)$ at $z_l$ into bounds at $z_r$ (`stepPiece`, `stepPiece_sound`).
--   3. Chaining pieces (`runPieces`), and `runCheck`, which certifies one chunk of a chain so that long chains can be checked in separate files (`runCheck_sound`).
--   4. Start near the singular point: any solution with $k/z\to 2a$, $P/z\to 2a$ satisfies $|k(z_1)-2az_1|,\ |P(z_1)-2az_1|\le \tfrac{3B}{8}z_1^3$ (`sing_start`).
--   5. Transfer: if $h$ is a shot with slope $a$ (`ShootSol a h`), then $(k,P)$ solves the system on $(0,1)$ with these limits at $0$, and $k(1)=h(\pi/2)$.
--
--   **Formalization Note.** Decisions use `decide +kernel` only (no `native_decide`).
-- source:
--   S. Gustafson, D. Meinert, C. Melcher, Saddle Point Configurations for Spherical Ferromagnets, arXiv:2509.05159v2, https://arxiv.org/abs/2509.05159, eq. (2.6), Definition 3.1, Remark 3.18; AIM open problems list, problem 241 (https://github.com/MColbrook/AIM). Supporting proof infrastructure for the disproof of SphericalFerromagnet.hemispheric_profile_unique.

import Mathlib
import Definitions.Def_spherical_ferromagnet_shooting_defs

/-! ## Poly -/

/-!
# Computable rational polynomials with real-evaluation soundness lemmas

Polynomials are lists of rational coefficients (lowest degree first).  All operations are
computable and are evaluated by the kernel (`decide +kernel`) in the numerical certificates.
-/

namespace P241N

abbrev Poly := List ℚ

def padd : Poly → Poly → Poly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q

def pscale (c : ℚ) (p : Poly) : Poly := p.map (c * ·)

def pmul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => padd (pscale a q) (0 :: pmul p q)

def pderiv : Poly → Poly
  | [] => []
  | _ :: q => padd q (0 :: pderiv q)

/-- `pshift p d` is the polynomial `t ↦ p (d + t)`. -/
def pshift (p : Poly) (d : ℚ) : Poly :=
  p.foldr (fun a acc => padd (pmul acc [d, 1]) [a]) []

def evalQ (p : Poly) (x : ℚ) : ℚ := p.foldr (fun a acc => a + x * acc) 0

noncomputable def evalR (p : Poly) (x : ℝ) : ℝ := p.foldr (fun a acc => (a : ℝ) + x * acc) 0

/-- `∑ |aᵢ| rⁱ`. -/
def absB (p : Poly) (r : ℚ) : ℚ := p.foldr (fun a acc => |a| + r * acc) 0

@[simp] lemma evalR_nil (x : ℝ) : evalR [] x = 0 := rfl
@[simp] lemma evalR_cons (a : ℚ) (p : Poly) (x : ℝ) :
    evalR (a :: p) x = a + x * evalR p x := rfl

lemma evalR_padd (p q : Poly) (x : ℝ) : evalR (padd p q) x = evalR p x + evalR q x := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons a p ih =>
    cases q with
    | nil => simp [padd]
    | cons b q => simp [padd, ih]; ring

lemma evalR_pscale (c : ℚ) (p : Poly) (x : ℝ) : evalR (pscale c p) x = c * evalR p x := by
  induction p with
  | nil => simp [pscale]
  | cons a p ih =>
    simp only [pscale, List.map_cons, evalR_cons] at ih ⊢
    rw [ih]; push_cast; ring

lemma evalR_pmul (p q : Poly) (x : ℝ) : evalR (pmul p q) x = evalR p x * evalR q x := by
  induction p with
  | nil => simp [pmul]
  | cons a p ih => simp [pmul, evalR_padd, evalR_pscale, ih]; ring

lemma evalR_pshift (p : Poly) (d : ℚ) (t : ℝ) : evalR (pshift p d) t = evalR p (d + t) := by
  induction p with
  | nil => simp [pshift]
  | cons a p ih =>
    have : pshift (a :: p) d = padd (pmul (pshift p d) [d, 1]) [a] := rfl
    rw [this, evalR_padd, evalR_pmul, ih]; simp; ring

lemma hasDerivAt_evalR (p : Poly) (x : ℝ) :
    HasDerivAt (fun y => evalR p y) (evalR (pderiv p) x) x := by
  induction p with
  | nil => simp only [pderiv, evalR_nil]; exact hasDerivAt_const x (0 : ℝ)
  | cons a p ih =>
    simp only [evalR_cons, pderiv, evalR_padd]
    have := ((hasDerivAt_id' x).mul ih).const_add (a : ℝ)
    exact this.congr_deriv (by simp)

lemma continuous_evalR (p : Poly) : Continuous (fun y => evalR p y) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_evalR p x).continuousAt

lemma evalQ_cast (p : Poly) (x : ℚ) : ((evalQ p x : ℚ) : ℝ) = evalR p x := by
  induction p with
  | nil => simp [evalQ]
  | cons a p ih =>
    simp only [evalQ, List.foldr_cons] at ih ⊢
    push_cast; rw [ih]; rfl

lemma absB_nonneg (p : Poly) {r : ℚ} (hr : 0 ≤ r) : 0 ≤ absB p r := by
  induction p with
  | nil => simp [absB]
  | cons a p ih =>
    simp only [absB, List.foldr_cons] at ih ⊢
    positivity

lemma abs_evalR_le (p : Poly) {r : ℚ} (hr : 0 ≤ r) {t : ℝ} (ht : |t| ≤ r) :
    |evalR p t| ≤ absB p r := by
  induction p with
  | nil => simp [absB]
  | cons a p ih =>
    simp only [evalR_cons]
    have h1 : (absB (a :: p) r : ℝ) = |(a : ℝ)| + r * absB p r := by
      simp [absB]
    rw [h1]
    calc |(a : ℝ) + t * evalR p t| ≤ |(a : ℝ)| + |t| * |evalR p t| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(a : ℝ)| + r * absB p r := by
          have := absB_nonneg p hr
          gcongr

end P241N

/-! ## Gron -/

/-!
# A Grönwall step on `ℝ × ℝ` with explicit rational exponential bound
-/

namespace P241N

open Set Real

/-- Rational upper bound for `exp x`, `0 ≤ x ≤ 1` (Taylor of order 6 with remainder). -/
def expUB (x : ℚ) : ℚ :=
  1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 * 7 / 4320

lemma exp_le_expUB {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ (expUB x : ℝ) := by
  have h := Real.exp_bound' (x := (x : ℝ)) (by exact_mod_cast h0) (by exact_mod_cast h1)
    (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  unfold expUB; push_cast
  convert h using 1; norm_num

lemma gronwallBound_le {δ K ε x U : ℝ} (hK : 0 < K) (hU : Real.exp (K * x) ≤ U)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    gronwallBound δ K ε x ≤ δ * U + ε / K * (U - 1) := by
  rw [gronwallBound_of_K_ne_0 hK.ne']
  have h1 : 0 ≤ ε / K := div_nonneg hε hK.le
  have h2 := mul_le_mul_of_nonneg_left hU hδ
  have h3 := mul_le_mul_of_nonneg_left (sub_le_sub_right hU 1) h1
  linarith

/-- One Grönwall step for an exact solution `f` and an approximate solution `g` of
`x' = v t x` on `[a, b]`, with all bounds explicit. -/
lemma gronwall_step {v : ℝ → ℝ × ℝ → ℝ × ℝ} {f g f' g' : ℝ → ℝ × ℝ} {a b K ε δ U : ℝ}
    (hK : 0 < K)
    (hv : ∀ t ∈ Ico a b, ∀ p q, dist (v t p) (v t q) ≤ K * dist p q)
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ t ∈ Ico a b, HasDerivAt f (f' t) t)
    (hfv : ∀ t ∈ Ico a b, f' t = v t (f t))
    (hg' : ∀ t, HasDerivAt g (g' t) t)
    (hgv : ∀ t ∈ Ico a b, dist (g' t) (v t (g t)) ≤ ε)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (ha : dist (f a) (g a) ≤ δ)
    (hU : Real.exp (K * (b - a)) ≤ U) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ δ * U + ε / K * (U - 1) := by
  intro t ht
  have hg : ContinuousOn g (Icc a b) :=
    fun t _ => (hg' t).continuousAt.continuousWithinAt
  have key := dist_le_of_approx_trajectories_ODE_of_mem (K := ⟨K, hK.le⟩) (s := fun _ => univ)
    (v := v) (εf := 0) (εg := ε)
    (fun t ht => LipschitzOnWith.of_dist_le_mul fun p _ q _ => hv t ht p q)
    hf (fun t ht => (hf' t ht).hasDerivWithinAt) (fun t ht => by rw [hfv t ht, dist_self])
    (fun _ _ => trivial) hg (fun t _ => (hg' t).hasDerivWithinAt) hgv (fun _ _ => trivial) ha
    t ht
  simp only [zero_add] at key
  refine key.trans ((gronwallBound_mono hδ hε hK.le (by linarith [ht.2] : t - a ≤ b - a)).trans ?_)
  exact gronwallBound_le hK hU hδ hε

end P241N

/-! ## Model -/

/-!
# The profile ODE in the variable `z = tan (θ/2)`

With `s = sin θ = 2z/(1+z²)`, `c = cos θ = (1-z²)/(1+z²)`, `k(z) = h(θ)` and `P = z k'`,
equation (2.6) at `κ = 4` becomes the first-order system
`k' = P / z`, `P' = Fz z k / z`, where `Fz z k = sin(2k)/2 + 2 s² sin(2k - 2θ)`,
written with `cos 2θ = C2 z`, `sin 2θ = S2 z` rational in `z`.
-/

namespace P241N

open Real

noncomputable def ssq (z : ℝ) : ℝ := 4 * z ^ 2 / (1 + z ^ 2) ^ 2
noncomputable def C2 (z : ℝ) : ℝ := ((1 + z ^ 2) ^ 2 - 8 * z ^ 2) / (1 + z ^ 2) ^ 2
noncomputable def S2 (z : ℝ) : ℝ := 4 * z * (1 - z ^ 2) / (1 + z ^ 2) ^ 2

noncomputable def Fz (z x : ℝ) : ℝ :=
  Real.sin (2 * x) / 2 + 2 * ssq z * (Real.sin (2 * x) * C2 z - Real.cos (2 * x) * S2 z)

/-- The approximate right-hand side with `X ≈ cos 2x`, `Y ≈ sin 2x`. -/
noncomputable def Ft (z X Y : ℝ) : ℝ := Y / 2 + 2 * ssq z * (Y * C2 z - X * S2 z)

lemma W_pos (z : ℝ) : 0 < 1 + z ^ 2 := by positivity

lemma C2_sq_add_S2_sq (z : ℝ) : C2 z ^ 2 + S2 z ^ 2 = 1 := by
  unfold C2 S2
  have := W_pos z
  field_simp
  ring

lemma abs_C2_le (z : ℝ) : |C2 z| ≤ 1 := by
  have := C2_sq_add_S2_sq z
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (S2 z), sq_nonneg (C2 z + 1), sq_nonneg (C2 z - 1)]

lemma abs_S2_le (z : ℝ) : |S2 z| ≤ 1 := by
  have := C2_sq_add_S2_sq z
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (C2 z), sq_nonneg (S2 z + 1), sq_nonneg (S2 z - 1)]

lemma ssq_nonneg (z : ℝ) : 0 ≤ ssq z := by unfold ssq; positivity

lemma ssq_le_one (z : ℝ) : ssq z ≤ 1 := by
  unfold ssq
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (z ^ 2 - 1)]

lemma ssq_mono {z w : ℝ} (hz : 0 ≤ z) (hzw : z ≤ w) (hw : w ≤ 1) : ssq z ≤ ssq w := by
  unfold ssq
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hzw1 : z * w ≤ 1 := by nlinarith
  have h1 : z * (1 + w ^ 2) ≤ w * (1 + z ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hzw) (sub_nonneg.2 hzw1)]
  have h2 : 0 ≤ z * (1 + w ^ 2) := by positivity
  have h3 := pow_le_pow_left₀ h2 h1 2
  nlinarith [h3]

lemma Fz_lip (z x y : ℝ) : |Fz z x - Fz z y| ≤ (1 + 4 * ssq z) * |x - y| := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => Fz z t)
      (Real.cos (2 * t) + 4 * ssq z * (Real.cos (2 * t) * C2 z + Real.sin (2 * t) * S2 z)) t := by
    intro t
    have hs : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * t) * 2) t := by
      simpa using ((hasDerivAt_id t).const_mul 2).sin
    have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-Real.sin (2 * t) * 2) t := by
      simpa using ((hasDerivAt_id t).const_mul 2).cos
    have := (hs.div_const 2).add (((hs.mul_const (C2 z)).sub (hc.mul_const (S2 z))).const_mul
      (2 * ssq z))
    unfold Fz
    exact this.congr_deriv (by ring)
  have hb : ∀ t : ℝ, ‖Real.cos (2 * t) + 4 * ssq z * (Real.cos (2 * t) * C2 z +
      Real.sin (2 * t) * S2 z)‖ ≤ 1 + 4 * ssq z := by
    intro t
    have hcs := C2_sq_add_S2_sq z
    have hsc := Real.sin_sq_add_cos_sq (2 * t)
    have h1 : |Real.cos (2 * t) * C2 z + Real.sin (2 * t) * S2 z| ≤ 1 := by
      rw [abs_le]; constructor <;>
      nlinarith [sq_nonneg (Real.cos (2 * t) * S2 z - Real.sin (2 * t) * C2 z),
        sq_nonneg (Real.cos (2 * t) * C2 z + Real.sin (2 * t) * S2 z - 1),
        sq_nonneg (Real.cos (2 * t) * C2 z + Real.sin (2 * t) * S2 z + 1)]
    rw [Real.norm_eq_abs]
    have h4 : 0 ≤ 4 * ssq z := by linarith [ssq_nonneg z]
    have h5 := Real.abs_cos_le_one (2 * t)
    calc _ ≤ |Real.cos (2 * t)| + |4 * ssq z * (Real.cos (2 * t) * C2 z +
          Real.sin (2 * t) * S2 z)| := abs_add_le _ _
      _ = |Real.cos (2 * t)| + 4 * ssq z * |Real.cos (2 * t) * C2 z +
          Real.sin (2 * t) * S2 z| := by rw [abs_mul, abs_of_nonneg h4]
      _ ≤ 1 + 4 * ssq z * 1 := by gcongr
      _ = _ := by ring
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t => Fz z t)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => hb t) convex_univ (Set.mem_univ y)
    (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

lemma Fz_sub_Ft (z x X Y E : ℝ) (hX : |Real.cos (2 * x) - X| ≤ E)
    (hY : |Real.sin (2 * x) - Y| ≤ E) : |Fz z x - Ft z X Y| ≤ (1 / 2 + 4 * ssq z) * E := by
  have e1 : Fz z x - Ft z X Y = (Real.sin (2 * x) - Y) / 2 + 2 * ssq z *
      ((Real.sin (2 * x) - Y) * C2 z - (Real.cos (2 * x) - X) * S2 z) := by
    unfold Fz Ft; ring
  rw [e1]
  have hs := ssq_nonneg z
  have hC := abs_C2_le z
  have hS := abs_S2_le z
  have hE : 0 ≤ E := (abs_nonneg _).trans hX
  calc _ ≤ |(Real.sin (2 * x) - Y) / 2| + |2 * ssq z *
        ((Real.sin (2 * x) - Y) * C2 z - (Real.cos (2 * x) - X) * S2 z)| := abs_add_le _ _
    _ ≤ E / 2 + 2 * ssq z * (E * 1 + E * 1) := by
        rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ssq z),
          abs_of_pos (by norm_num : (0:ℝ) < 2)]
        gcongr
        calc _ ≤ |(Real.sin (2 * x) - Y) * C2 z| + |(Real.cos (2 * x) - X) * S2 z| :=
              abs_sub _ _
          _ ≤ E * 1 + E * 1 := by
              rw [abs_mul, abs_mul]
              gcongr
    _ = _ := by ring

/-- Polynomial form of `(1+z²)⁴ (z q' - Ft)`. -/
lemma D2_identity (z q' X Y : ℝ) :
    (1 + z ^ 2) ^ 4 * (z * q' - Ft z X Y) =
      (1 + z ^ 2) ^ 4 * (z * q' - Y / 2) -
        8 * z ^ 2 * (Y * ((1 + z ^ 2) ^ 2 - 8 * z ^ 2) - X * (4 * z * (1 - z ^ 2))) := by
  unfold Ft ssq C2 S2
  have := W_pos z
  field_simp
  ring

end P241N

/-! ## Check -/

/-!
# A kernel-checkable a-posteriori enclosure for the `z`-system

`stepPiece` takes error bounds valid at the left end of a piece and returns error bounds valid
at its right end; `stepPiece_sound` proves this for every exact solution of the system.
-/

namespace P241N

open Set Real

/-- A solution of `k' = P/z`, `P' = Fz z k / z` on `[z0, 1]`. -/
structure IsSol (k P : ℝ → ℝ) (z0 : ℝ) : Prop where
  pos : 0 < z0
  cont_k : ContinuousOn k (Icc z0 1)
  cont_P : ContinuousOn P (Icc z0 1)
  dk : ∀ z ∈ Ico z0 1, HasDerivAt k (P z / z) z
  dP : ∀ z ∈ Ico z0 1, HasDerivAt P (Fz z (k z) / z) z

/-- Polynomial data on a segment, in the local variable `z - c`:
`G ≈ k`, `Q ≈ P`, `X ≈ cos (2G)`, `Y ≈ sin (2G)`. -/
structure Seg where
  c : ℚ
  G : Poly
  Q : Poly
  X : Poly
  Y : Poly

noncomputable def Seg.g (s : Seg) (z : ℝ) : ℝ := evalR s.G (z - s.c)
noncomputable def Seg.q (s : Seg) (z : ℝ) : ℝ := evalR s.Q (z - s.c)
noncomputable def Seg.x (s : Seg) (z : ℝ) : ℝ := evalR s.X (z - s.c)
noncomputable def Seg.y (s : Seg) (z : ℝ) : ℝ := evalR s.Y (z - s.c)

/-- The invariant: error bounds `e` for `(k, P)` and `E` for `(cos 2G, sin 2G)` at `z`. -/
def Inv (k P : ℝ → ℝ) (s : Seg) (z e E : ℝ) : Prop :=
  |k z - s.g z| ≤ e ∧ |P z - s.q z| ≤ e ∧
    |Real.cos (2 * s.g z) - s.x z| ≤ E ∧ |Real.sin (2 * s.g z) - s.y z| ≤ E

/-- Round up to the dyadic grid `2^-64`. -/
def rup (x : ℚ) : ℚ := ((⌈x * 2 ^ 64⌉ : ℤ) : ℚ) / 2 ^ 64

lemma le_rup (x : ℚ) : x ≤ rup x := by
  unfold rup
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

/-- Shifted polynomials and defect polynomials of a piece, in the variable `t = z - m`. -/
structure PCalc where
  m : ℚ
  r : ℚ
  G : Poly
  Q : Poly
  X : Poly
  Y : Poly
  D1 : Poly
  D2 : Poly
  D3 : Poly
  D4 : Poly

def mkCalc (zl zr : ℚ) (s : Seg) : PCalc :=
  let m := (zl + zr) / 2
  let d := m - s.c
  let G := pshift s.G d
  let Q := pshift s.Q d
  let X := pshift s.X d
  let Y := pshift s.Y d
  let zp : Poly := [m, 1]
  let z2 := pmul zp zp
  let W := padd [1] z2
  let W2 := pmul W W
  let W4 := pmul W2 W2
  { m := m, r := (zr - zl) / 2, G := G, Q := Q, X := X, Y := Y
    D1 := padd (pmul zp (pderiv G)) (pscale (-1) Q)
    D2 := padd (pmul W4 (padd (pmul zp (pderiv Q)) (pscale (-1/2) Y)))
      (pscale (-8) (pmul z2 (padd (pmul Y (padd W2 (pscale (-8) z2)))
        (pscale (-1) (pmul X (pscale 4 (pmul zp (padd [1] (pscale (-1) z2)))))))))
    D3 := padd (pderiv X) (pscale 2 (pmul (pderiv G) Y))
    D4 := padd (pderiv Y) (pscale (-2) (pmul (pderiv G) X)) }

def KEof (zl zr : ℚ) (s : Seg) : ℚ :=
  2 * absB (pderiv (mkCalc zl zr s).G) (mkCalc zl zr s).r + 1 / 2 ^ 64

def Enew (zl zr : ℚ) (s : Seg) (E : ℚ) : ℚ :=
  rup (E * expUB (KEof zl zr s * (zr - zl)) +
    max (absB (mkCalc zl zr s).D3 (mkCalc zl zr s).r) (absB (mkCalc zl zr s).D4 (mkCalc zl zr s).r)
      / KEof zl zr s * (expUB (KEof zl zr s * (zr - zl)) - 1))

def sqOf (zr : ℚ) : ℚ := 4 * zr ^ 2 / (1 + zr ^ 2) ^ 2

def Kof (zl zr : ℚ) : ℚ := (1 + 4 * sqOf zr) / zl

def epsOf (zl zr : ℚ) (s : Seg) (E : ℚ) : ℚ :=
  max (absB (mkCalc zl zr s).D1 (mkCalc zl zr s).r / zl)
    ((absB (mkCalc zl zr s).D2 (mkCalc zl zr s).r / (1 + zl ^ 2) ^ 4 +
      (1 / 2 + 4 * sqOf zr) * Enew zl zr s E) / zl)

def enew (zl zr : ℚ) (s : Seg) (e E : ℚ) : ℚ :=
  rup (e * expUB (Kof zl zr * (zr - zl)) +
    epsOf zl zr s E / Kof zl zr * (expUB (Kof zl zr * (zr - zl)) - 1))

def stepOK (zl zr : ℚ) (s : Seg) (e E : ℚ) : Prop :=
  0 < zl ∧ zl < zr ∧ zr ≤ 1 ∧ KEof zl zr s * (zr - zl) ≤ 1 ∧ Kof zl zr * (zr - zl) ≤ 1 ∧
    0 ≤ e ∧ 0 ≤ E

instance (zl zr : ℚ) (s : Seg) (e E : ℚ) : Decidable (stepOK zl zr s e E) := by
  unfold stepOK; infer_instance

def stepPiece (zl zr : ℚ) (s : Seg) (e E : ℚ) : Option (ℚ × ℚ) :=
  if stepOK zl zr s e E then some (enew zl zr s e E, Enew zl zr s E) else none

/-! ### Semantics of `mkCalc` -/

section calc_lemmas
variable (zl zr : ℚ) (s : Seg) (z : ℝ)

lemma calc_G : evalR (mkCalc zl zr s).G (z - (mkCalc zl zr s).m) = s.g z := by
  simp only [mkCalc, Seg.g, evalR_pshift]; congr 1; push_cast; ring
lemma calc_Q : evalR (mkCalc zl zr s).Q (z - (mkCalc zl zr s).m) = s.q z := by
  simp only [mkCalc, Seg.q, evalR_pshift]; congr 1; push_cast; ring
lemma calc_X : evalR (mkCalc zl zr s).X (z - (mkCalc zl zr s).m) = s.x z := by
  simp only [mkCalc, Seg.x, evalR_pshift]; congr 1; push_cast; ring
lemma calc_Y : evalR (mkCalc zl zr s).Y (z - (mkCalc zl zr s).m) = s.y z := by
  simp only [mkCalc, Seg.y, evalR_pshift]; congr 1; push_cast; ring

variable (t : ℝ)

lemma calc_D1 : evalR (mkCalc zl zr s).D1 t =
    ((mkCalc zl zr s).m + t) * evalR (pderiv (mkCalc zl zr s).G) t - evalR (mkCalc zl zr s).Q t := by
  simp only [mkCalc, evalR_padd, evalR_pmul, evalR_pscale, evalR_cons, evalR_nil]; push_cast; ring

lemma calc_D2 : evalR (mkCalc zl zr s).D2 t =
    (1 + ((mkCalc zl zr s).m + t) ^ 2) ^ 4 * (((mkCalc zl zr s).m + t) *
        evalR (pderiv (mkCalc zl zr s).Q) t - evalR (mkCalc zl zr s).Y t / 2) -
      8 * ((mkCalc zl zr s).m + t) ^ 2 * (evalR (mkCalc zl zr s).Y t *
        ((1 + ((mkCalc zl zr s).m + t) ^ 2) ^ 2 - 8 * ((mkCalc zl zr s).m + t) ^ 2) -
        evalR (mkCalc zl zr s).X t * (4 * ((mkCalc zl zr s).m + t) *
          (1 - ((mkCalc zl zr s).m + t) ^ 2))) := by
  simp only [mkCalc, evalR_padd, evalR_pmul, evalR_pscale, evalR_cons, evalR_nil]; push_cast; ring

lemma calc_D3 : evalR (mkCalc zl zr s).D3 t = evalR (pderiv (mkCalc zl zr s).X) t +
    2 * (evalR (pderiv (mkCalc zl zr s).G) t * evalR (mkCalc zl zr s).Y t) := by
  simp only [mkCalc, evalR_padd, evalR_pmul, evalR_pscale]; push_cast; ring

lemma calc_D4 : evalR (mkCalc zl zr s).D4 t = evalR (pderiv (mkCalc zl zr s).Y) t -
    2 * (evalR (pderiv (mkCalc zl zr s).G) t * evalR (mkCalc zl zr s).X t) := by
  simp only [mkCalc, evalR_padd, evalR_pmul, evalR_pscale]; push_cast; ring

end calc_lemmas

lemma hasDerivAt_shift (p : Poly) (m : ℚ) (z : ℝ) :
    HasDerivAt (fun z => evalR p (z - m)) (evalR (pderiv p) (z - m)) z := by
  exact HasDerivAt.comp_sub_const z (m : ℝ) (hasDerivAt_evalR p (z - m))

lemma abs_sub_mid_le {zl zr : ℚ} {z : ℝ} (hz : z ∈ Icc (zl : ℝ) zr) :
    |z - (((zl + zr) / 2 : ℚ) : ℝ)| ≤ (((zr - zl) / 2 : ℚ) : ℝ) := by
  push_cast; rw [abs_le]; constructor <;> linarith [hz.1, hz.2]

lemma dist_prod_le {a b c d M : ℝ} (h1 : |a - c| ≤ M) (h2 : |b - d| ≤ M) :
    dist (a, b) (c, d) ≤ M := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact max_le h1 h2

lemma abs_le_of_dist_prod {a b c d M : ℝ} (h : dist (a, b) (c, d) ≤ M) :
    |a - c| ≤ M ∧ |b - d| ≤ M := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at h
  exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩

end P241N

/-! ## StepSound -/

/-!
# Soundness of one piece of the enclosure
-/

namespace P241N

open Set Real

lemma le_rup_cast (x : ℚ) : (x : ℝ) ≤ (rup x : ℝ) := by exact_mod_cast le_rup x

lemma abs_snd_sub_le (p q : ℝ × ℝ) : |p.2 - q.2| ≤ dist p q := by
  rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_right _ _

lemma abs_fst_sub_le (p q : ℝ × ℝ) : |p.1 - q.1| ≤ dist p q := by
  rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_left _ _

theorem stepPiece_sound {k P : ℝ → ℝ} {z0 : ℝ} (hsol : IsSol k P z0) {zl zr : ℚ} {s : Seg}
    {e E : ℚ} (hz0 : z0 ≤ zl) (hok : stepOK zl zr s e E) (hinv : Inv k P s zl e E) :
    Inv k P s zr (enew zl zr s e E) (Enew zl zr s E) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hok
  set pc := mkCalc zl zr s with hpc
  have hm : pc.m = (zl + zr) / 2 := rfl
  have hr : pc.r = (zr - zl) / 2 := rfl
  have hr0 : (0 : ℚ) ≤ pc.r := by rw [hr]; linarith
  have hab : (zl : ℝ) ≤ zr := by exact_mod_cast h1.le
  have hzl0 : (0 : ℝ) < zl := by exact_mod_cast h0
  -- polynomial bounds on the piece
  have hpb : ∀ p : Poly, ∀ z ∈ Icc (zl : ℝ) zr, |evalR p (z - pc.m)| ≤ absB p pc.r := by
    intro p z hz
    apply abs_evalR_le p hr0
    rw [hm, hr]; exact abs_sub_mid_le hz
  -- derivatives of the approximants
  have hgfun : (fun z => s.g z) = fun z => evalR pc.G (z - pc.m) := funext fun z => (calc_G _ _ _ z).symm
  have hqfun : (fun z => s.q z) = fun z => evalR pc.Q (z - pc.m) := funext fun z => (calc_Q _ _ _ z).symm
  have hxfun : (fun z => s.x z) = fun z => evalR pc.X (z - pc.m) := funext fun z => (calc_X _ _ _ z).symm
  have hyfun : (fun z => s.y z) = fun z => evalR pc.Y (z - pc.m) := funext fun z => (calc_Y _ _ _ z).symm
  set γ : ℝ → ℝ := fun z => evalR (pderiv pc.G) (z - pc.m) with hγ
  have hG' : ∀ z, HasDerivAt (fun z => s.g z) (γ z) z := by
    intro z; rw [hgfun]; exact hasDerivAt_shift _ _ z
  have hQ' : ∀ z, HasDerivAt (fun z => s.q z) (evalR (pderiv pc.Q) (z - pc.m)) z := by
    intro z; rw [hqfun]; exact hasDerivAt_shift _ _ z
  have hX' : ∀ z, HasDerivAt (fun z => s.x z) (evalR (pderiv pc.X) (z - pc.m)) z := by
    intro z; rw [hxfun]; exact hasDerivAt_shift _ _ z
  have hY' : ∀ z, HasDerivAt (fun z => s.y z) (evalR (pderiv pc.Y) (z - pc.m)) z := by
    intro z; rw [hyfun]; exact hasDerivAt_shift _ _ z
  ------------------------------------------------------------------
  -- Step 1: rotation tracking of (cos 2G, sin 2G)
  ------------------------------------------------------------------
  have hKE : (0 : ℝ) < KEof zl zr s := by
    have : (0 : ℚ) < KEof zl zr s := by
      unfold KEof; have := absB_nonneg (pderiv pc.G) hr0; positivity
    exact_mod_cast this
  have hγb : ∀ z ∈ Icc (zl : ℝ) zr, |2 * γ z| ≤ KEof zl zr s := by
    intro z hz
    have := hpb (pderiv pc.G) z hz
    unfold KEof; push_cast
    rw [abs_mul, abs_two]
    have : (0 : ℝ) ≤ 1 / 2 ^ 64 := by positivity
    simp only [hγ]; linarith
  have stepE : ∀ z ∈ Icc (zl : ℝ) zr,
      dist (Real.cos (2 * s.g z), Real.sin (2 * s.g z)) (s.x z, s.y z) ≤ Enew zl zr s E := by
    have hEn := le_rup_cast (E * expUB (KEof zl zr s * (zr - zl)) +
      max (absB pc.D3 pc.r) (absB pc.D4 pc.r) / KEof zl zr s *
        (expUB (KEof zl zr s * (zr - zl)) - 1))
    have hεω : (0 : ℝ) ≤ max (absB pc.D3 pc.r : ℝ) (absB pc.D4 pc.r) :=
      le_max_of_le_left (by exact_mod_cast absB_nonneg _ hr0)
    have key := gronwall_step (a := (zl : ℝ)) (b := zr) (K := KEof zl zr s)
      (ε := max (absB pc.D3 pc.r : ℝ) (absB pc.D4 pc.r)) (δ := E)
      (U := expUB (KEof zl zr s * (zr - zl)))
      (v := fun z p => (-(2 * γ z) * p.2, 2 * γ z * p.1))
      (f := fun z => (Real.cos (2 * s.g z), Real.sin (2 * s.g z)))
      (f' := fun z => (-Real.sin (2 * s.g z) * (2 * γ z), Real.cos (2 * s.g z) * (2 * γ z)))
      (g := fun z => (s.x z, s.y z))
      (g' := fun z => (evalR (pderiv pc.X) (z - pc.m), evalR (pderiv pc.Y) (z - pc.m)))
      hKE
      (by
        intro z hz p q
        have hb := hγb z (Ico_subset_Icc_self hz)
        have hd0 := dist_nonneg (x := p) (y := q)
        apply dist_prod_le
        · rw [← mul_sub, abs_mul, abs_neg]
          exact (mul_le_mul hb (abs_snd_sub_le p q) (abs_nonneg _) hKE.le)
        · rw [← mul_sub, abs_mul]
          exact (mul_le_mul hb (abs_fst_sub_le p q) (abs_nonneg _) hKE.le))
      (by
        have hc : Continuous fun z => s.g z := continuous_iff_continuousAt.2 fun z =>
          (hG' z).continuousAt
        have hc2 : Continuous fun z => 2 * s.g z := continuous_const.mul hc
        exact ((Real.continuous_cos.comp hc2).prodMk (Real.continuous_sin.comp hc2)).continuousOn)
      (fun z _ => (((hG' z).const_mul 2).cos).prodMk (((hG' z).const_mul 2).sin))
      (fun z _ => by simp only [Prod.mk.injEq]; constructor <;> ring)
      (fun z => (hX' z).prodMk (hY' z))
      (by
        intro z hz
        have hz' := Ico_subset_Icc_self hz
        apply dist_prod_le
        · have e3 : evalR (pderiv pc.X) (z - pc.m) - -(2 * γ z) * s.y z =
              evalR pc.D3 (z - pc.m) := by
            rw [hpc, calc_D3, ← calc_Y zl zr s z]; simp only [hγ, hpc]; ring
          rw [e3]; exact (hpb _ z hz').trans (le_max_left _ _)
        · have e4 : evalR (pderiv pc.Y) (z - pc.m) - 2 * γ z * s.x z =
              evalR pc.D4 (z - pc.m) := by
            rw [hpc, calc_D4, ← calc_X zl zr s z]; simp only [hγ, hpc]; ring
          rw [e4]; exact (hpb _ z hz').trans (le_max_right _ _))
      hεω (by exact_mod_cast h6)
      (dist_prod_le hinv.2.2.1 hinv.2.2.2)
      (by
        have := exp_le_expUB (x := KEof zl zr s * (zr - zl))
          (by have := hKE; have : (0:ℚ) < KEof zl zr s := by exact_mod_cast this
              nlinarith) h3
        push_cast at this; exact this)
    intro z hz
    refine (key z hz).trans ?_
    push_cast at hEn ⊢
    unfold Enew;
    exact hEn
  ------------------------------------------------------------------
  -- Step 2: the main system
  ------------------------------------------------------------------
  have hsq : ∀ z ∈ Icc (zl : ℝ) zr, ssq z ≤ sqOf zr := by
    intro z hz
    have := ssq_mono (le_trans hzl0.le hz.1) hz.2 (by exact_mod_cast h2)
    unfold sqOf; push_cast; unfold ssq at this; exact this
  have hsq0 : (0 : ℝ) ≤ sqOf zr := by
    have : (0 : ℚ) ≤ sqOf zr := by unfold sqOf; positivity
    exact_mod_cast this
  have hK : (0 : ℝ) < Kof zl zr := by
    unfold Kof; push_cast; positivity
  have hKz : ∀ z ∈ Icc (zl : ℝ) zr, (1 + 4 * ssq z) / z ≤ Kof zl zr := by
    intro z hz
    unfold Kof; push_cast
    have hz0 : 0 < z := lt_of_lt_of_le hzl0 hz.1
    calc (1 + 4 * ssq z) / z ≤ (1 + 4 * sqOf zr) / z := by
          gcongr; exact hsq z hz
      _ ≤ (1 + 4 * (sqOf zr : ℝ)) / zl := by
          apply div_le_div_of_nonneg_left (by positivity) hzl0 hz.1
  have hKz1 : ∀ z ∈ Icc (zl : ℝ) zr, 1 / z ≤ Kof zl zr := by
    intro z hz
    refine le_trans ?_ (hKz z hz)
    have hz0 : 0 < z := lt_of_lt_of_le hzl0 hz.1
    gcongr; linarith [ssq_nonneg z]
  have hsub : Icc (zl : ℝ) zr ⊆ Icc z0 1 := by
    intro z hz; exact ⟨le_trans hz0 hz.1, le_trans hz.2 (by exact_mod_cast h2)⟩
  have hsubo : Ico (zl : ℝ) zr ⊆ Ico z0 1 := by
    intro z hz; exact ⟨le_trans hz0 hz.1, lt_of_lt_of_le hz.2 (by exact_mod_cast h2)⟩
  have hen := le_rup_cast (e * expUB (Kof zl zr * (zr - zl)) +
    epsOf zl zr s E / Kof zl zr * (expUB (Kof zl zr * (zr - zl)) - 1))
  have hε0 : (0 : ℝ) ≤ epsOf zl zr s E := by
    have : (0 : ℚ) ≤ epsOf zl zr s E := by
      unfold epsOf
      exact le_max_of_le_left (div_nonneg (absB_nonneg _ hr0) h0.le)
    exact_mod_cast this
  have key := gronwall_step (a := (zl : ℝ)) (b := zr) (K := Kof zl zr)
    (ε := epsOf zl zr s E) (δ := e) (U := expUB (Kof zl zr * (zr - zl)))
    (v := fun z p => (p.2 / z, Fz z p.1 / z))
    (f := fun z => (k z, P z)) (f' := fun z => (P z / z, Fz z (k z) / z))
    (g := fun z => (s.g z, s.q z))
    (g' := fun z => (γ z, evalR (pderiv pc.Q) (z - pc.m)))
    hK
    (by
      intro z hz p q
      have hz' := Ico_subset_Icc_self hz
      have hzpos : 0 < z := lt_of_lt_of_le hzl0 hz.1
      apply dist_prod_le
      · rw [← sub_div, abs_div, abs_of_pos hzpos, div_eq_mul_one_div, mul_comm]
        exact mul_le_mul (hKz1 z hz') (abs_snd_sub_le p q) (abs_nonneg _) hK.le
      · rw [← sub_div, abs_div, abs_of_pos hzpos]
        calc |Fz z p.1 - Fz z q.1| / z ≤ (1 + 4 * ssq z) * |p.1 - q.1| / z := by
              gcongr; exact Fz_lip z p.1 q.1
          _ = (1 + 4 * ssq z) / z * |p.1 - q.1| := by ring
          _ ≤ Kof zl zr * dist p q := by
              apply mul_le_mul (hKz z hz') (abs_fst_sub_le p q) (abs_nonneg _) hK.le)
    ((hsol.cont_k.mono hsub).prodMk (hsol.cont_P.mono hsub))
    (fun z hz => (hsol.dk z (hsubo hz)).prodMk (hsol.dP z (hsubo hz)))
    (fun z _ => rfl)
    (fun z => (hG' z).prodMk (hQ' z))
    (by
      intro z hz
      have hz' := Ico_subset_Icc_self hz
      have hzpos : 0 < z := lt_of_lt_of_le hzl0 hz.1
      have hW : (1 + (zl : ℝ) ^ 2) ^ 4 ≤ (1 + z ^ 2) ^ 4 := by
        gcongr; exact hz.1
      have hW0 : (0 : ℝ) < (1 + (zl : ℝ) ^ 2) ^ 4 := by positivity
      have hzm : (pc.m : ℝ) + (z - pc.m) = z := by ring
      apply dist_prod_le
      · -- |G' - Q/z| ≤ A1/zl
        have hA := hpb pc.D1 z hz'
        rw [calc_D1, hzm, calc_Q] at hA
        have : γ z - s.q z / z = (z * γ z - s.q z) / z := by field_simp
        rw [this, abs_div, abs_of_pos hzpos]
        unfold epsOf; push_cast
        refine le_trans ?_ (le_max_left _ _)
        calc |z * γ z - s.q z| / z ≤ (absB pc.D1 pc.r : ℝ) / z := by gcongr
          _ ≤ (absB pc.D1 pc.r : ℝ) / zl := by
            gcongr
            · exact_mod_cast absB_nonneg _ hr0
            · exact hz.1
      · -- |Q' - Fz z G / z|
        have hA := hpb pc.D2 z hz'
        rw [calc_D2, hzm, calc_Y, calc_X, ← D2_identity] at hA
        have hE := stepE z hz'
        obtain ⟨hEc, hEs⟩ := abs_le_of_dist_prod hE
        have hF := Fz_sub_Ft z (s.g z) (s.x z) (s.y z) _ hEc hEs
        set Q' := evalR (pderiv pc.Q) (z - pc.m)
        have h1' : |z * Q' - Ft z (s.x z) (s.y z)| ≤ (absB pc.D2 pc.r : ℝ) / (1 + (zl : ℝ) ^ 2) ^ 4 := by
          rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < (1 + z ^ 2) ^ 4)] at hA
          rw [le_div_iff₀ hW0]
          calc |z * Q' - Ft z (s.x z) (s.y z)| * (1 + (zl : ℝ) ^ 2) ^ 4
              ≤ |z * Q' - Ft z (s.x z) (s.y z)| * (1 + z ^ 2) ^ 4 := by gcongr
            _ ≤ _ := by rw [mul_comm]; exact hA
        have hEn0 : (0 : ℝ) ≤ Enew zl zr s E := (abs_nonneg _).trans hEc
        have h2' : |Fz z (s.g z) - Ft z (s.x z) (s.y z)| ≤ (1 / 2 + 4 * sqOf zr) * Enew zl zr s E :=
          hF.trans (by gcongr; exact hsq z hz')
        have : Q' - Fz z (s.g z) / z = (z * Q' - Fz z (s.g z)) / z := by field_simp
        rw [this, abs_div, abs_of_pos hzpos]
        unfold epsOf; push_cast
        refine le_trans ?_ (le_max_right _ _)
        have h3' : |z * Q' - Fz z (s.g z)| ≤ (absB pc.D2 pc.r : ℝ) / (1 + (zl : ℝ) ^ 2) ^ 4 +
            (1 / 2 + 4 * sqOf zr) * Enew zl zr s E := by
          calc |z * Q' - Fz z (s.g z)| ≤ |z * Q' - Ft z (s.x z) (s.y z)| +
                |Fz z (s.g z) - Ft z (s.x z) (s.y z)| := by
                rw [abs_sub_comm (Fz _ _)]; exact abs_sub_le _ _ _
            _ ≤ _ := add_le_add h1' h2'
        have hnum0 : (0 : ℝ) ≤ (absB pc.D2 pc.r : ℝ) / (1 + (zl : ℝ) ^ 2) ^ 4 +
            (1 / 2 + 4 * sqOf zr) * Enew zl zr s E := (abs_nonneg _).trans h3'
        calc |z * Q' - Fz z (s.g z)| / z ≤ _ / z := by gcongr
          _ ≤ _ / (zl : ℝ) := by gcongr; exact hz.1)
    hε0 (by exact_mod_cast h5)
    (dist_prod_le hinv.1 hinv.2.1)
    (by
      have := exp_le_expUB (x := Kof zl zr * (zr - zl))
        (by have : (0:ℚ) < Kof zl zr := by exact_mod_cast hK
            nlinarith) h4
      push_cast at this; exact this)
  have hb : (zr : ℝ) ∈ Icc (zl : ℝ) zr := ⟨hab, le_rfl⟩
  have hmain := abs_le_of_dist_prod (key zr hb)
  have hrot := abs_le_of_dist_prod (stepE zr hb)
  have hfin : (e : ℝ) * expUB (Kof zl zr * (zr - zl)) + epsOf zl zr s E / Kof zl zr *
      (expUB (Kof zl zr * (zr - zl)) - 1) ≤ (enew zl zr s e E : ℝ) := by
    unfold enew; push_cast at hen ⊢; exact hen
  exact ⟨hmain.1.trans hfin, hmain.2.trans hfin, hrot.1, hrot.2⟩

end P241N

/-! ## Run -/

/-!
# Chaining pieces, initial bounds, and the final enclosure
-/

namespace P241N

open Set Real

structure Piece where
  zl : ℚ
  zr : ℚ
  s : Seg

def dG (s s' : Seg) (z : ℚ) : ℚ := |evalQ s'.G (z - s'.c) - evalQ s.G (z - s.c)|
def dQ (s s' : Seg) (z : ℚ) : ℚ := |evalQ s'.Q (z - s'.c) - evalQ s.Q (z - s.c)|
def dX (s s' : Seg) (z : ℚ) : ℚ := |evalQ s'.X (z - s'.c) - evalQ s.X (z - s.c)|
def dY (s s' : Seg) (z : ℚ) : ℚ := |evalQ s'.Y (z - s'.c) - evalQ s.Y (z - s.c)|

def runPieces : Seg → ℚ → ℚ → ℚ → List Piece → Option (Seg × ℚ × ℚ × ℚ)
  | s, z, e, E, [] => some (s, z, e, E)
  | s, z, e, E, p :: ps =>
    if z = p.zl then
      let e1 := e + max (dG s p.s z) (dQ s p.s z)
      let E1 := E + 2 * dG s p.s z + max (dX s p.s z) (dY s p.s z)
      match stepPiece p.zl p.zr p.s e1 E1 with
      | some (e2, E2) => runPieces p.s p.zr e2 E2 ps
      | none => none
    else none

lemma evalR_rat (p : Poly) (z c : ℚ) : evalR p ((z : ℝ) - c) = (evalQ p (z - c) : ℝ) := by
  rw [evalQ_cast]; push_cast; rfl

lemma abs_sub_le3 (a b c d : ℝ) : |a - d| ≤ |a - b| + |b - c| + |c - d| := by
  have h1 := abs_sub_le a b d
  have h2 := abs_sub_le b c d
  linarith

lemma jump_sound {k P : ℝ → ℝ} {s s' : Seg} {z e E : ℚ} (h : Inv k P s z e E) :
    Inv k P s' z ((e + max (dG s s' z) (dQ s s' z) : ℚ) : ℝ)
      ((E + 2 * dG s s' z + max (dX s s' z) (dY s s' z) : ℚ) : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have eG : |s.g z - s'.g z| = (dG s s' z : ℝ) := by
    simp only [Seg.g, dG, evalR_rat]; push_cast; rw [abs_sub_comm]
  have eQ : |s.q z - s'.q z| = (dQ s s' z : ℝ) := by
    simp only [Seg.q, dQ, evalR_rat]; push_cast; rw [abs_sub_comm]
  have eX : |s.x z - s'.x z| = (dX s s' z : ℝ) := by
    simp only [Seg.x, dX, evalR_rat]; push_cast; rw [abs_sub_comm]
  have eY : |s.y z - s'.y z| = (dY s s' z : ℝ) := by
    simp only [Seg.y, dY, evalR_rat]; push_cast; rw [abs_sub_comm]
  have mG : (dG s s' z : ℝ) ≤ max (dG s s' z : ℝ) (dQ s s' z) := le_max_left _ _
  have mQ : (dQ s s' z : ℝ) ≤ max (dG s s' z : ℝ) (dQ s s' z) := le_max_right _ _
  have mX : (dX s s' z : ℝ) ≤ max (dX s s' z : ℝ) (dY s s' z) := le_max_left _ _
  have mY : (dY s s' z : ℝ) ≤ max (dX s s' z : ℝ) (dY s s' z) := le_max_right _ _
  have cG : |Real.cos (2 * s'.g z) - Real.cos (2 * s.g z)| ≤ 2 * (dG s s' z : ℝ) := by
    refine (Real.abs_cos_sub_cos_le _ _).trans (le_of_eq ?_)
    rw [← eG, ← mul_sub, abs_mul, abs_two, abs_sub_comm]
  have sG : |Real.sin (2 * s'.g z) - Real.sin (2 * s.g z)| ≤ 2 * (dG s s' z : ℝ) := by
    refine (Real.abs_sin_sub_sin_le _ _).trans (le_of_eq ?_)
    rw [← eG, ← mul_sub, abs_mul, abs_two, abs_sub_comm]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc |k z - s'.g z| ≤ |k z - s.g z| + |s.g z - s'.g z| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  · calc |P z - s'.q z| ≤ |P z - s.q z| + |s.q z - s'.q z| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  · calc |Real.cos (2 * s'.g z) - s'.x z| ≤ |Real.cos (2 * s'.g z) - Real.cos (2 * s.g z)| +
          |Real.cos (2 * s.g z) - s.x z| + |s.x z - s'.x z| := abs_sub_le3 _ _ _ _
      _ ≤ _ := by linarith
  · calc |Real.sin (2 * s'.g z) - s'.y z| ≤ |Real.sin (2 * s'.g z) - Real.sin (2 * s.g z)| +
          |Real.sin (2 * s.g z) - s.y z| + |s.y z - s'.y z| := abs_sub_le3 _ _ _ _
      _ ≤ _ := by linarith

theorem runPieces_sound {k P : ℝ → ℝ} {z0 : ℝ} (hsol : IsSol k P z0) :
    ∀ (ps : List Piece) (s : Seg) (z e E : ℚ) (res : Seg × ℚ × ℚ × ℚ),
      z0 ≤ z → Inv k P s z e E → runPieces s z e E ps = some res →
        z0 ≤ res.2.1 ∧ Inv k P res.1 res.2.1 res.2.2.1 res.2.2.2
  | [], s, z, e, E, res, hz, hinv, h => by
    simp only [runPieces, Option.some.injEq] at h
    subst h; exact ⟨hz, hinv⟩
  | p :: ps, s, z, e, E, res, hz, hinv, h => by
    simp only [runPieces] at h
    split_ifs at h with hzp
    · split at h
      · rename_i e2 E2 hstep
        unfold stepPiece at hstep
        split_ifs at hstep with hok
        simp only [Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨rfl, rfl⟩ := hstep
        subst hzp
        have hj := jump_sound (s' := p.s) hinv
        have hstep' := stepPiece_sound hsol hz hok hj
        have hz' : z0 ≤ p.zr := le_trans hz (by exact_mod_cast hok.2.1.le)
        exact runPieces_sound hsol ps p.s p.zr _ _ res hz' hstep' h
      · simp at h

/-! ### Initial and final bounds -/

/-- Initial error bound at `z0`, from the singular-start bound `sing`. -/
def e0 (a z0 sing : ℚ) (s : Seg) : ℚ :=
  sing + max |2 * a * z0 - evalQ s.G (z0 - s.c)| |2 * a * z0 - evalQ s.Q (z0 - s.c)|

def E0 (z0 : ℚ) (s : Seg) : ℚ :=
  let x := 2 * evalQ s.G (z0 - s.c)
  max (|1 - x ^ 2 / 2 - evalQ s.X (z0 - s.c)| + |x| ^ 4 * (5 / 96))
      (|x - x ^ 3 / 6 - evalQ s.Y (z0 - s.c)| + |x| ^ 5 / 100)

def initOK (z0 : ℚ) (s : Seg) : Bool := decide (|2 * evalQ s.G (z0 - s.c)| ≤ 1)

lemma init_sound {k P : ℝ → ℝ} {a z0 sing : ℚ} {s : Seg}
    (hk : |k z0 - 2 * a * z0| ≤ sing) (hP : |P z0 - 2 * a * z0| ≤ sing)
    (hok : initOK z0 s = true) : Inv k P s z0 (e0 a z0 sing s) (E0 z0 s) := by
  simp only [initOK, decide_eq_true_eq] at hok
  have hg : s.g z0 = (evalQ s.G (z0 - s.c) : ℝ) := evalR_rat _ _ _
  have hq : s.q z0 = (evalQ s.Q (z0 - s.c) : ℝ) := evalR_rat _ _ _
  have hx : s.x z0 = (evalQ s.X (z0 - s.c) : ℝ) := evalR_rat _ _ _
  have hy : s.y z0 = (evalQ s.Y (z0 - s.c) : ℝ) := evalR_rat _ _ _
  have hx1 : |((2 * evalQ s.G (z0 - s.c) : ℚ) : ℝ)| ≤ 1 := by exact_mod_cast hok
  have hcb := Real.cos_bound hx1
  have hsb := Real.sin_bound hx1
  unfold Inv e0 E0
  rw [hg, hq, hx, hy]
  push_cast [Rat.cast_abs, Rat.cast_max] at hcb hsb ⊢
  set g : ℝ := (evalQ s.G (z0 - s.c) : ℝ)
  set q : ℝ := (evalQ s.Q (z0 - s.c) : ℝ)
  set X : ℝ := (evalQ s.X (z0 - s.c) : ℝ)
  set Y : ℝ := (evalQ s.Y (z0 - s.c) : ℝ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc |k z0 - g| ≤ |k z0 - 2 * a * z0| + |2 * a * z0 - g| := abs_sub_le _ _ _
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · calc |P z0 - q| ≤ |P z0 - 2 * a * z0| + |2 * a * z0 - q| := abs_sub_le _ _ _
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · refine le_trans ?_ (le_max_left _ _)
    calc _ ≤ |Real.cos (2 * g) - (1 - (2 * g) ^ 2 / 2)| + |1 - (2 * g) ^ 2 / 2 - X| :=
          abs_sub_le _ _ _
      _ ≤ _ := by linarith
  · refine le_trans ?_ (le_max_right _ _)
    calc _ ≤ |Real.sin (2 * g) - (2 * g - (2 * g) ^ 3 / 6)| + |2 * g - (2 * g) ^ 3 / 6 - Y| :=
          abs_sub_le _ _ _
      _ ≤ _ := by linarith

/-- Lower bound on `k 1` certified by a run. -/
def lowerCheck (a z0 sing : ℚ) (s0 : Seg) (ps : List Piece) (L : ℚ) : Bool :=
  initOK z0 s0 &&
  match runPieces s0 z0 (e0 a z0 sing s0) (E0 z0 s0) ps with
  | some (s, z, e, _) => decide (z = 1) && decide (L < evalQ s.G (1 - s.c) - e)
  | none => false

/-- Upper bound on `k 1` certified by a run. -/
def upperCheck (a z0 sing : ℚ) (s0 : Seg) (ps : List Piece) (L : ℚ) : Bool :=
  initOK z0 s0 &&
  match runPieces s0 z0 (e0 a z0 sing s0) (E0 z0 s0) ps with
  | some (s, z, e, _) => decide (z = 1) && decide (evalQ s.G (1 - s.c) + e < L)
  | none => false

theorem lowerCheck_sound {k P : ℝ → ℝ} {a z0 sing L : ℚ} {s0 : Seg} {ps : List Piece}
    (hsol : IsSol k P z0) (hk : |k z0 - 2 * a * z0| ≤ sing) (hP : |P z0 - 2 * a * z0| ≤ sing)
    (hc : lowerCheck a z0 sing s0 ps L = true) : (L : ℝ) < k 1 := by
  unfold lowerCheck at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hi, hc⟩ := hc
  have hinv := init_sound hk hP hi
  split at hc
  · rename_i s z e E hrun
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hz1, hL⟩ := hc
    have := (runPieces_sound hsol ps s0 z0 _ _ _ le_rfl hinv hrun).2
    simp only at this
    subst hz1
    have h1 := this.1
    have hg : s.g ((1 : ℚ) : ℝ) = (evalQ s.G (1 - s.c) : ℝ) := evalR_rat _ _ _
    rw [hg] at h1
    have hL' : (L : ℝ) < (evalQ s.G (1 - s.c) : ℝ) - e := by exact_mod_cast hL
    push_cast at h1
    have := (abs_le.1 h1).1
    linarith
  · simp at hc

theorem upperCheck_sound {k P : ℝ → ℝ} {a z0 sing L : ℚ} {s0 : Seg} {ps : List Piece}
    (hsol : IsSol k P z0) (hk : |k z0 - 2 * a * z0| ≤ sing) (hP : |P z0 - 2 * a * z0| ≤ sing)
    (hc : upperCheck a z0 sing s0 ps L = true) : k 1 < L := by
  unfold upperCheck at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hi, hc⟩ := hc
  have hinv := init_sound hk hP hi
  split at hc
  · rename_i s z e E hrun
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hz1, hL⟩ := hc
    have := (runPieces_sound hsol ps s0 z0 _ _ _ le_rfl hinv hrun).2
    simp only at this
    subst hz1
    have h1 := this.1
    have hg : s.g ((1 : ℚ) : ℝ) = (evalQ s.G (1 - s.c) : ℝ) := evalR_rat _ _ _
    rw [hg] at h1
    have hL' : (evalQ s.G (1 - s.c) : ℝ) + e < L := by exact_mod_cast hL
    push_cast at h1
    have := (abs_le.1 h1).2
    linarith
  · simp at hc

end P241N

/-! ## Singular -/

/-!
# Singular start: a priori bounds near `z = 0` for any solution

For any solution of `k' = P/z`, `P' = Fz z k / z` on `(0, z1]` with `k/z → 2a`, `P/z → 2a`,
we get `|k z1 - 2 a z1| ≤ 3 B z1³ / 8` and `|P z1 - 2 a z1| ≤ 3 B z1³ / 8`, where
`B = (2/3) K³ + 16 (K + 2)`, `K = 2|a| + η`, provided `3 B z1² / 8 < η`.
The proof uses `(z (P - k))' = Fz - k`, `((P + k)/z)' = (Fz - k)/z²` and a continuity
(first-crossing) argument for the bound `|k| < K z`.
-/

namespace P241N

open Set Real Filter Topology

lemma abs_sin_sub_self_le (y : ℝ) : |Real.sin y - y| ≤ |y| ^ 3 / 6 := by
  have pos : ∀ y : ℝ, 0 ≤ y → |Real.sin y - y| ≤ y ^ 3 / 6 := by
    intro y hy
    rcases hy.eq_or_lt with h | h
    · subst h; simp
    · have h1 := Real.sin_le hy
      have h2 := Real.sin_gt_sub_cube h
      rw [abs_le]; constructor <;> linarith
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact pos y hy
  · have := pos (-y) (by linarith)
    rw [Real.sin_neg, abs_of_nonpos hy] at *
    rw [show -Real.sin y - -y = -(Real.sin y - y) by ring, abs_neg] at this
    simpa [neg_pow, Odd.neg_one_pow (by decide : Odd 3)] using this

lemma N_bound {z x K : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) (hK : 0 ≤ K) (hx : |x| ≤ K * z) :
    |Fz z x - x| ≤ ((2 / 3) * K ^ 3 + 16 * (K + 2)) * z ^ 3 := by
  have hW : 1 ≤ (1 + z ^ 2) ^ 2 := by nlinarith [sq_nonneg z]
  have hW0 : 0 < (1 + z ^ 2) ^ 2 := by positivity
  have hs : ssq z ≤ 4 * z ^ 2 := by
    unfold ssq; rw [div_le_iff₀ hW0]; nlinarith [sq_nonneg z]
  have hS : |S2 z| ≤ 4 * z := by
    unfold S2
    rw [abs_div, abs_of_pos hW0, div_le_iff₀ hW0, abs_mul, abs_of_pos (by positivity : 0 < 4 * z)]
    have : |1 - z ^ 2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 4 * z)]
  have e1 : Fz z x - x = (Real.sin (2 * x) - 2 * x) / 2 +
      2 * ssq z * (Real.sin (2 * x) * C2 z - Real.cos (2 * x) * S2 z) := by
    unfold Fz; ring
  have h1 : |(Real.sin (2 * x) - 2 * x) / 2| ≤ (2 / 3) * K ^ 3 * z ^ 3 := by
    rw [abs_div, abs_two]
    have := abs_sin_sub_self_le (2 * x)
    rw [abs_mul, abs_two] at this
    have hx3 : |x| ^ 3 ≤ (K * z) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hx 3
    have : (2 * |x|) ^ 3 / 6 / 2 = (2 / 3) * |x| ^ 3 := by ring
    nlinarith
  have h2 : |Real.sin (2 * x) * C2 z - Real.cos (2 * x) * S2 z| ≤ 2 * K * z + 4 * z := by
    have t1 := abs_sub (Real.sin (2 * x) * C2 z) (Real.cos (2 * x) * S2 z)
    have t2 := mul_le_mul (Real.abs_sin_le_abs (x := 2 * x)) (abs_C2_le z) (abs_nonneg _)
      (abs_nonneg _)
    have t3 := mul_le_mul (Real.abs_cos_le_one (2 * x)) hS (abs_nonneg _) zero_le_one
    rw [abs_mul, abs_mul] at t1
    rw [abs_mul, abs_two] at t2
    nlinarith
  have hs0 := ssq_nonneg z
  rw [e1]
  calc _ ≤ |(Real.sin (2 * x) - 2 * x) / 2| +
        |2 * ssq z * (Real.sin (2 * x) * C2 z - Real.cos (2 * x) * S2 z)| := abs_add_le _ _
    _ ≤ (2 / 3) * K ^ 3 * z ^ 3 + 2 * (4 * z ^ 2) * (2 * K * z + 4 * z) := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ssq z)]
        gcongr
    _ = _ := by ring

lemma bound_of_tendsto {f : ℝ → ℝ} {L C c w : ℝ} (hw : 0 < w)
    (hf : Tendsto f (𝓝[>] 0) (𝓝 L)) (h : ∀ ε ∈ Ioo 0 w, |c - f ε| ≤ C) : |c - L| ≤ C := by
  have ht : Tendsto (fun ε => |c - f ε|) (𝓝[>] 0) (𝓝 |c - L|) :=
    (tendsto_const_nhds.sub hf).abs
  exact le_of_tendsto ht (Filter.mem_of_superset (Ioo_mem_nhdsGT hw) fun ε hε => h ε hε)

/-- Hypotheses on a solution near the singular point. -/
structure NearZero (k P : ℝ → ℝ) (a z1 : ℝ) : Prop where
  pos : 0 < z1
  le1 : z1 ≤ 1
  ck : ContinuousOn k (Ioc 0 z1)
  cP : ContinuousOn P (Ioc 0 z1)
  dk : ∀ z ∈ Ioo 0 z1, HasDerivAt k (P z / z) z
  dP : ∀ z ∈ Ioo 0 z1, HasDerivAt P (Fz z (k z) / z) z
  lk : Tendsto (fun z => k z / z) (𝓝[>] 0) (𝓝 (2 * a))
  lP : Tendsto (fun z => P z / z) (𝓝[>] 0) (𝓝 (2 * a))

lemma sing_est {k P : ℝ → ℝ} {a z1 K : ℝ} (hs : NearZero k P a z1) (hK : 0 ≤ K)
    {w : ℝ} (hw : w ∈ Ioc 0 z1) (hb : ∀ z ∈ Ioo 0 w, |k z| ≤ K * z) :
    |k w - 2 * a * w| ≤ 3 * ((2 / 3) * K ^ 3 + 16 * (K + 2)) * w ^ 3 / 8 ∧
      |P w - 2 * a * w| ≤ 3 * ((2 / 3) * K ^ 3 + 16 * (K + 2)) * w ^ 3 / 8 := by
  set B := (2 / 3) * K ^ 3 + 16 * (K + 2) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hw0 := hw.1
  have hsub : ∀ x ∈ Ioo 0 w, x ∈ Ioo 0 z1 := fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hw.2⟩
  have hNb : ∀ x ∈ Ioo 0 w, |Fz x (k x) - k x| ≤ B * x ^ 3 := fun x hx =>
    N_bound hx.1 (le_trans (le_trans hx.2.le hw.2) hs.le1) hK (hb x hx)
  -- Φ = x (P - k)
  have hΦ : ∀ x ∈ Ioo 0 w, HasDerivAt (fun x => x * (P x - k x)) (Fz x (k x) - k x) x := by
    intro x hx
    have := (hasDerivAt_id' x).mul ((hs.dP x (hsub x hx)).sub (hs.dk x (hsub x hx)))
    refine this.congr_deriv ?_
    field_simp [hx.1.ne']; simp only [Pi.sub_apply, Pi.add_apply]; ring
  have hΨ : ∀ x ∈ Ioo 0 w, HasDerivAt (fun x => (P x + k x) / x) ((Fz x (k x) - k x) / x ^ 2) x := by
    intro x hx
    have := ((hs.dP x (hsub x hx)).add (hs.dk x (hsub x hx))).div (hasDerivAt_id' x) hx.1.ne'
    refine this.congr_deriv ?_
    field_simp [hx.1.ne']; simp only [Pi.sub_apply, Pi.add_apply]; ring
  have hcont : ∀ ε ∈ Ioo 0 w, Icc ε w ⊆ Ioc 0 z1 := fun ε hε x hx =>
    ⟨lt_of_lt_of_le hε.1 hx.1, le_trans hx.2 hw.2⟩
  -- estimate for Φ
  have hΦb : ∀ ε ∈ Ioo 0 w, |w * (P w - k w) - ε * (P ε - k ε)| ≤ B * w ^ 4 / 4 := by
    intro ε hε
    have hc : ContinuousOn (fun x => x * (P x - k x) - ε * (P ε - k ε)) (Icc ε w) :=
      ((continuousOn_id.mul ((hs.cP.mono (hcont ε hε)).sub (hs.ck.mono (hcont ε hε)))).sub
        continuousOn_const)
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := ε) (b := w)
      (f := fun x => x * (P x - k x) - ε * (P ε - k ε)) (f' := fun x => Fz x (k x) - k x)
      (B := fun x => B * (x ^ 4 - ε ^ 4) / 4) (B' := fun x => B * x ^ 3) hc
      (fun x hx => ((hΦ x ⟨lt_of_lt_of_le hε.1 hx.1, hx.2⟩).sub_const _).hasDerivWithinAt)
      (by simp)
      (fun x => by
        have := (((hasDerivAt_pow 4 x).sub_const (ε ^ 4)).const_mul B).div_const 4
        exact this.congr_deriv (by norm_num; ring))
      (fun x hx => by
        rw [Real.norm_eq_abs]; exact hNb x ⟨lt_of_lt_of_le hε.1 hx.1, hx.2⟩)
      (x := w) ⟨hε.2.le, le_rfl⟩
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have : 0 ≤ B * ε ^ 4 := by have := hε.1; positivity
    nlinarith
  have hΨb : ∀ ε ∈ Ioo 0 w, |(P w + k w) / w - (P ε + k ε) / ε| ≤ B * w ^ 2 / 2 := by
    intro ε hε
    have hc : ContinuousOn (fun x => (P x + k x) / x - (P ε + k ε) / ε) (Icc ε w) :=
      (((hs.cP.mono (hcont ε hε)).add (hs.ck.mono (hcont ε hε))).div continuousOn_id
        (fun x hx => (lt_of_lt_of_le hε.1 hx.1).ne')).sub continuousOn_const
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := ε) (b := w)
      (f := fun x => (P x + k x) / x - (P ε + k ε) / ε)
      (f' := fun x => (Fz x (k x) - k x) / x ^ 2)
      (B := fun x => B * (x ^ 2 - ε ^ 2) / 2) (B' := fun x => B * x) hc
      (fun x hx => ((hΨ x ⟨lt_of_lt_of_le hε.1 hx.1, hx.2⟩).sub_const _).hasDerivWithinAt)
      (by simp)
      (fun x => by
        have := (((hasDerivAt_pow 2 x).sub_const (ε ^ 2)).const_mul B).div_const 2
        exact this.congr_deriv (by norm_num; ring))
      (fun x hx => by
        have hx0 : 0 < x := lt_of_lt_of_le hε.1 hx.1
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < x ^ 2),
          div_le_iff₀ (by positivity)]
        have := hNb x ⟨hx0, hx.2⟩
        calc _ ≤ B * x ^ 3 := this
          _ = B * x * x ^ 2 := by ring)
      (x := w) ⟨hε.2.le, le_rfl⟩
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have : 0 ≤ B * ε ^ 2 := by have := hε.1; positivity
    nlinarith
  -- limits
  have lΦ : Tendsto (fun ε => ε * (P ε - k ε)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => ε ^ 2 * (P ε / ε - k ε / ε)) (𝓝[>] 0)
        (𝓝 (0 ^ 2 * (2 * a - 2 * a))) :=
      ((continuous_pow 2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
        (hs.lP.sub hs.lk)
    simp only [sub_self, mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have : ε ≠ 0 := (show (0:ℝ) < ε from hε).ne'
    field_simp
  have lΨ : Tendsto (fun ε => (P ε + k ε) / ε) (𝓝[>] 0) (𝓝 (4 * a)) := by
    have h1 := hs.lP.add hs.lk
    rw [show 2 * a + 2 * a = 4 * a by ring] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [add_div]
  have bΦ := bound_of_tendsto hw0 lΦ hΦb
  have bΨ := bound_of_tendsto hw0 lΨ hΨb
  rw [sub_zero] at bΦ
  have ek : k w - 2 * a * w = (w * ((P w + k w) / w - 4 * a) - w * (P w - k w) / w) / 2 := by
    field_simp; ring
  have eP : P w - 2 * a * w = (w * ((P w + k w) / w - 4 * a) + w * (P w - k w) / w) / 2 := by
    field_simp; ring
  have t1 : |w * ((P w + k w) / w - 4 * a)| ≤ w * (B * w ^ 2 / 2) := by
    rw [abs_mul, abs_of_pos hw0]; gcongr
  have t2 : |w * (P w - k w) / w| ≤ B * w ^ 4 / 4 / w := by
    rw [abs_div, abs_of_pos hw0]; gcongr
  have t3 : B * w ^ 4 / 4 / w = B * w ^ 3 / 4 := by field_simp
  constructor
  · rw [ek, abs_div, abs_two]
    have := abs_sub (w * ((P w + k w) / w - 4 * a)) (w * (P w - k w) / w)
    nlinarith
  · rw [eP, abs_div, abs_two]
    have := abs_add_le (w * ((P w + k w) / w - 4 * a)) (w * (P w - k w) / w)
    nlinarith

/-- The singular-start theorem. -/
theorem sing_start {k P : ℝ → ℝ} {a z1 η : ℝ} (hs : NearZero k P a z1) (hη : 0 < η)
    (hsmall : 3 * ((2 / 3) * (2 * |a| + η) ^ 3 + 16 * ((2 * |a| + η) + 2)) * z1 ^ 2 / 8 < η) :
    |k z1 - 2 * a * z1| ≤ 3 * ((2 / 3) * (2 * |a| + η) ^ 3 + 16 * ((2 * |a| + η) + 2)) * z1 ^ 3 / 8 ∧
      |P z1 - 2 * a * z1| ≤
        3 * ((2 / 3) * (2 * |a| + η) ^ 3 + 16 * ((2 * |a| + η) + 2)) * z1 ^ 3 / 8 := by
  set K := 2 * |a| + η with hKdef
  have hK : 0 ≤ K := by positivity
  set B := (2 / 3) * K ^ 3 + 16 * (K + 2)
  -- the bootstrap: |k z| < K z on (0, z1]
  have hboot : ∀ z ∈ Ioc 0 z1, |k z| < K * z := by
    by_contra hcon
    push Not at hcon
    -- near 0 the bound holds strictly
    have hlim : ∀ᶠ z in 𝓝[>] (0:ℝ), |k z / z| < K := by
      have := (continuous_abs.tendsto _).comp hs.lk
      have h2 : |2 * a| < K := by rw [abs_mul, abs_two]; linarith
      exact this.eventually (gt_mem_nhds h2)
    obtain ⟨ε0, hε0, hε0b⟩ := Metric.mem_nhdsWithin_iff.1 hlim
    have hsmallz : ∀ z, 0 < z → z < ε0 → |k z| < K * z := by
      intro z hz hzε
      have : |k z / z| < K := hε0b ⟨by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hz]; exact hzε, hz⟩
      rw [abs_div, abs_of_pos hz, div_lt_iff₀ hz] at this
      linarith
    set ε1 := min (ε0 / 2) z1
    have hε1 : 0 < ε1 := lt_min (by linarith) hs.pos
    let T := {z ∈ Icc ε1 z1 | K * z ≤ |k z|}
    have hTc : IsCompact T := by
      apply isCompact_Icc.of_isClosed_subset _ (fun z hz => hz.1)
      have hc : ContinuousOn (fun z => K * z - |k z|) (Icc ε1 z1) :=
        (continuousOn_const.mul continuousOn_id).sub
          ((hs.ck.mono fun z hz => ⟨lt_of_lt_of_le hε1 hz.1, hz.2⟩).abs)
      have := hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := (0:ℝ)))
      convert this using 1
      ext z; simp [T, sub_nonpos]
    obtain ⟨z, hz, hzb⟩ := hcon
    have hzT : z ∈ T := by
      refine ⟨⟨?_, hz.2⟩, hzb⟩
      by_contra hlt; push Not at hlt
      have : z < ε0 := lt_of_lt_of_le hlt (le_trans (min_le_left _ _) (by linarith))
      exact absurd hzb (not_le.2 (hsmallz z hz.1 this))
    obtain ⟨zs, hzsT, hzsmin⟩ := hTc.exists_isLeast ⟨z, hzT⟩
    have hzs0 : 0 < zs := lt_of_lt_of_le hε1 hzsT.1.1
    have hb : ∀ y ∈ Ioo 0 zs, |k y| ≤ K * y := by
      intro y hy
      by_cases hy1 : y < ε1
      · exact (hsmallz y hy.1 (lt_of_lt_of_le hy1 (le_trans (min_le_left _ _) (by linarith)))).le
      · push Not at hy1
        by_contra hk; push Not at hk
        have : y ∈ T := ⟨⟨hy1, le_trans hy.2.le hzsT.1.2⟩, hk.le⟩
        exact absurd (hzsmin this) (not_le.2 hy.2)
    have est := (sing_est hs hK ⟨hzs0, hzsT.1.2⟩ hb).1
    have hz3 : zs ^ 2 ≤ z1 ^ 2 := pow_le_pow_left₀ hzs0.le hzsT.1.2 2
    have hB0 : 0 ≤ B := by positivity
    have : |k zs| ≤ 2 * |a| * zs + 3 * B * zs ^ 3 / 8 := by
      have h1 := abs_sub_abs_le_abs_sub (k zs) (2 * a * zs)
      have est' : |k zs - 2 * a * zs| ≤ 3 * B * zs ^ 3 / 8 := est
      have h0 : |2 * a * zs| = 2 * |a| * zs := by
        rw [abs_mul, abs_mul, abs_two, abs_of_pos hzs0]
      linarith
    have h2 : 3 * B * zs ^ 3 / 8 < η * zs := by
      have : 3 * B * zs ^ 3 / 8 = (3 * B * zs ^ 2 / 8) * zs := by ring
      rw [this]
      apply mul_lt_mul_of_pos_right _ hzs0
      calc 3 * B * zs ^ 2 / 8 ≤ 3 * B * z1 ^ 2 / 8 := by gcongr
        _ < η := hsmall
    have h3 := hzsT.2
    have : K * zs = 2 * |a| * zs + η * zs := by rw [hKdef]; ring
    linarith
  exact sing_est hs hK ⟨hs.pos, le_rfl⟩ fun z hz => (hboot z ⟨hz.1, hz.2.le⟩).le

end P241N

/-! ## Transfer -/

/-!
# From `ShootSol a h` (variable `θ`) to the `z = tan (θ/2)` system

`k z = h (2 arctan z)`, `P z = sin (2 arctan z) * h'(2 arctan z)` (with `h'` the derivative
within `[0, π/2]`).
-/

namespace P241N

open Set Real Filter Topology SphericalFerromagnet
open scoped ContDiff

noncomputable def thz (z : ℝ) : ℝ := 2 * arctan z

lemma sqrt_sq_W (z : ℝ) : √(1 + z ^ 2) * √(1 + z ^ 2) = 1 + z ^ 2 :=
  Real.mul_self_sqrt (by positivity)

lemma sin_thz (z : ℝ) : Real.sin (thz z) = 2 * z / (1 + z ^ 2) := by
  unfold thz
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  have := sqrt_sq_W z
  have h0 : 0 < √(1 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  field_simp
  rw [Real.sq_sqrt (by positivity)]

lemma cos_thz (z : ℝ) : Real.cos (thz z) = (1 - z ^ 2) / (1 + z ^ 2) := by
  unfold thz
  rw [Real.cos_two_mul, Real.cos_arctan]
  have := sqrt_sq_W z
  have h0 : 0 < √(1 + z ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hW : (0:ℝ) < 1 + z ^ 2 := by positivity
  rw [div_pow, Real.sq_sqrt hW.le]
  field_simp
  ring

lemma Fz_eq (z x : ℝ) :
    Fz z x = Real.sin (2 * x) / 2 + 2 * Real.sin (thz z) ^ 2 * Real.sin (2 * x - 2 * thz z) := by
  have hW : (0:ℝ) < 1 + z ^ 2 := by positivity
  rw [Real.sin_sub, Real.sin_two_mul (thz z), Real.cos_two_mul (thz z), sin_thz, cos_thz]
  unfold Fz ssq C2 S2
  field_simp
  ring

lemma thz_mem {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) : thz z ∈ Ioo 0 (π / 2) := by
  unfold thz
  constructor
  · have := Real.arctan_strictMono hz.1  -- arctan 0 < arctan z
    rw [Real.arctan_zero] at this; linarith
  · have := Real.arctan_strictMono hz.2
    rw [Real.arctan_one] at this; linarith

lemma thz_mem_Icc {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : thz z ∈ Icc 0 (π / 2) := by
  unfold thz
  constructor
  · have := Real.arctan_strictMono.monotone hz.1
    rw [Real.arctan_zero] at this; linarith
  · have := Real.arctan_strictMono.monotone hz.2
    rw [Real.arctan_one] at this; linarith

lemma thz_one : thz 1 = π / 2 := by unfold thz; rw [Real.arctan_one]; ring

lemma hasDerivAt_thz (z : ℝ) : HasDerivAt thz (2 / (1 + z ^ 2)) z := by
  have := (Real.hasDerivAt_arctan z).const_mul 2
  have e : thz = fun x => 2 * arctan x := rfl
  rw [e]; exact this.congr_deriv (by field_simp)

lemma continuous_thz : Continuous thz := continuous_const.mul Real.continuous_arctan

section

variable {a : ℝ} {h : ℝ → ℝ}

noncomputable def hd (h : ℝ → ℝ) : ℝ → ℝ := derivWithin h (Icc 0 (π / 2))

noncomputable def kz (h : ℝ → ℝ) (z : ℝ) : ℝ := h (thz z)
noncomputable def Pz (h : ℝ → ℝ) (z : ℝ) : ℝ := Real.sin (thz z) * hd h (thz z)

lemma one_le_infty : (1 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top

lemma hasDerivAt_h (hs : ShootSol a h) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    HasDerivAt h (hd h θ) θ := by
  have hdiff := (hs.1.differentiableOn (by simp)) θ (Ioo_subset_Icc_self hθ)
  exact hdiff.hasDerivWithinAt.hasDerivAt (Icc_mem_nhds hθ.1 hθ.2)

lemma hd_eq_deriv (hs : ShootSol a h) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    hd h θ = deriv h θ := (hasDerivAt_h hs hθ).deriv.symm

lemma hasDerivAt_hd (hs : ShootSol a h) {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    HasDerivAt (hd h) (deriv (deriv h) θ) θ := by
  have h1 : ContDiffOn ℝ 1 (deriv h) (Ioo 0 (π / 2)) :=
    (hs.1.mono Ioo_subset_Icc_self).deriv_of_isOpen isOpen_Ioo (by
      rw [show (1 : WithTop ℕ∞) + 1 = ((2 : ℕ∞) : WithTop ℕ∞) by rfl]
      exact WithTop.coe_le_coe.2 le_top)
  have h2 : DifferentiableAt ℝ (deriv h) θ :=
    (h1.differentiableOn one_ne_zero θ hθ).differentiableAt (Ioo_mem_nhds hθ.1 hθ.2)
  refine h2.hasDerivAt.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with y hy
  exact hd_eq_deriv hs hy

lemma kz_deriv (hs : ShootSol a h) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (kz h) (Pz h z / z) z := by
  have := (hasDerivAt_h hs (thz_mem hz)).comp z (hasDerivAt_thz z)
  refine this.congr_deriv ?_
  unfold Pz; rw [sin_thz]
  have := hz.1.ne'
  field_simp

lemma Pz_deriv (hs : ShootSol a h) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (Pz h) (Fz z (kz h z) / z) z := by
  have hθ := thz_mem hz
  set θ := thz z with hθdef
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h1 := ((Real.hasDerivAt_sin θ).comp z (hasDerivAt_thz z)).mul
    ((hasDerivAt_hd hs hθ).comp z (hasDerivAt_thz z))
  have hode := hs.2.2.2 θ hθ
  unfold profileOperator at hode
  rw [← hd_eq_deriv hs hθ] at hode
  refine h1.congr_deriv ?_
  rw [Fz_eq, kz, ← hθdef]
  have hz0 := hz.1.ne'
  have hW : (0:ℝ) < 1 + z ^ 2 := by positivity
  have hsz : Real.sin θ = 2 * z / (1 + z ^ 2) := by rw [hθdef, sin_thz]
  -- solve the ODE for h''
  have hh2 : deriv (deriv h) θ = -(Real.cos θ / Real.sin θ * hd h θ)
      + Real.sin (2 * h θ) / (2 * Real.sin θ ^ 2) + 4 / 2 * Real.sin (2 * h θ - 2 * θ) := by
    linarith
  simp only [Function.comp]
  rw [hh2]
  field_simp
  rw [hsz]
  field_simp
  ring

lemma kz_cont (hs : ShootSol a h) : ContinuousOn (kz h) (Icc 0 1) := by
  have hc : ContinuousOn h (Icc 0 (π / 2)) := hs.1.continuousOn
  exact hc.comp continuous_thz.continuousOn fun z hz => thz_mem_Icc hz

lemma hd_cont (hs : ShootSol a h) : ContinuousOn (hd h) (Icc 0 (π / 2)) :=
  hs.1.continuousOn_derivWithin (uniqueDiffOn_Icc (by positivity)) one_le_infty

lemma Pz_cont (hs : ShootSol a h) : ContinuousOn (Pz h) (Icc 0 1) := by
  exact (Real.continuous_sin.comp continuous_thz).continuousOn.mul
    ((hd_cont hs).comp continuous_thz.continuousOn fun z hz => thz_mem_Icc hz)

lemma thz_tendsto : Tendsto thz (𝓝[>] 0) (𝓝[Icc 0 (π / 2) \ {0}] 0) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · have := continuous_thz.tendsto 0
    simp only [thz, Real.arctan_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with z hz
    have := thz_mem hz
    exact ⟨Ioo_subset_Icc_self this, this.1.ne'⟩

lemma thz_div_tendsto : Tendsto (fun z => thz z / z) (𝓝[>] 0) (𝓝 2) := by
  have h1 := (hasDerivAt_thz 0).tendsto_slope_zero_right
  simp only [zero_add, thz, Real.arctan_zero, mul_zero, sub_zero] at h1
  norm_num at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  unfold thz; field_simp

lemma kz_lim (hs : ShootSol a h) : Tendsto (fun z => kz h z / z) (𝓝[>] 0) (𝓝 (2 * a)) := by
  have hd0 : HasDerivWithinAt h a (Icc 0 (π / 2)) 0 := by
    have := ((hs.1.differentiableOn (by simp)) 0 ⟨le_rfl, by positivity⟩).hasDerivWithinAt
    rwa [hs.2.2.1] at this
  have h1 := (hasDerivWithinAt_iff_tendsto_slope.1 hd0).comp thz_tendsto
  have h2 := h1.mul thz_div_tendsto
  rw [mul_comm] at h2
  refine h2.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with z hz
  have hθ := (thz_mem hz).1.ne'
  simp only [Function.comp, slope_def_field, hs.2.1, sub_zero, kz]
  field_simp

lemma Pz_lim (hs : ShootSol a h) : Tendsto (fun z => Pz h z / z) (𝓝[>] 0) (𝓝 (2 * a)) := by
  have h1 : Tendsto (fun z => hd h (thz z)) (𝓝[>] 0) (𝓝 a) := by
    have hc := (hd_cont hs) 0 ⟨le_rfl, by positivity⟩
    have : hd h 0 = a := hs.2.2.1
    rw [← this]
    exact hc.tendsto.comp (thz_tendsto.mono_right (nhdsWithin_mono _ sdiff_subset))
  have h2 : Tendsto (fun z : ℝ => 2 / (1 + z ^ 2)) (𝓝[>] 0) (𝓝 2) := by
    have : Continuous fun z : ℝ => 2 / (1 + z ^ 2) :=
      continuous_const.div (by fun_prop) fun z => by positivity
    have := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have := h2.mul h1
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have : z ≠ 0 := (show (0:ℝ) < z from hz).ne'
  unfold Pz; rw [sin_thz]; field_simp

lemma kz_one : kz h 1 = h (π / 2) := by unfold kz; rw [thz_one]

end

end P241N

/-! ## Splitting a run into independently checked chunks -/

namespace P241N

open Set Real

/-- The segment that is active after running the pieces `ps` from segment `s`. -/
def lastSeg (s : Seg) : List Piece → Seg
  | [] => s
  | p :: ps => lastSeg p.s ps

lemma runPieces_seg : ∀ (ps : List Piece) (s : Seg) (z e E : ℚ) (r : Seg × ℚ × ℚ × ℚ),
    runPieces s z e E ps = some r → r.1 = lastSeg s ps
  | [], s, z, e, E, r, h => by
    simp only [runPieces, Option.some.injEq] at h
    subst h; rfl
  | p :: ps, s, z, e, E, r, h => by
    simp only [runPieces] at h
    split_ifs at h with hzp
    · split at h
      · exact runPieces_seg ps p.s _ _ _ r h
      · simp at h

lemma Inv.mono {k P : ℝ → ℝ} {s : Seg} {z e E e' E' : ℝ} (h : Inv k P s z e E)
    (he : e ≤ e') (hE : E ≤ E') : Inv k P s z e' E' :=
  ⟨h.1.trans he, h.2.1.trans he, h.2.2.1.trans hE, h.2.2.2.trans hE⟩

/-- A chunk of a run: starting from bounds `(e, E)` at `z` on segment `s`, the pieces `ps`
end at `z'` with bounds at most `(e', E')`. -/
def runCheck (s : Seg) (z e E : ℚ) (ps : List Piece) (z' e' E' : ℚ) : Bool :=
  match runPieces s z e E ps with
  | some (_, z1, e1, E1) => decide (z1 = z') && decide (e1 ≤ e') && decide (E1 ≤ E')
  | none => false

theorem runCheck_sound {k P : ℝ → ℝ} {z0 : ℝ} (hsol : IsSol k P z0) {s : Seg}
    {z e E z' e' E' : ℚ} {ps : List Piece} (hz : z0 ≤ z) (hinv : Inv k P s z e E)
    (hc : runCheck s z e E ps z' e' E' = true) :
    z0 ≤ z' ∧ Inv k P (lastSeg s ps) z' e' E' := by
  unfold runCheck at hc
  split at hc
  · rename_i s1 z1 e1 E1 hrun
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨rfl, he⟩, hE⟩ := hc
    have hr := runPieces_sound hsol ps s z e E _ hz hinv hrun
    have hs := runPieces_seg ps s z e E _ hrun
    simp only at hr hs
    rw [← hs]
    exact ⟨hr.1, hr.2.mono (by exact_mod_cast he) (by exact_mod_cast hE)⟩
  · simp at hc

/-- Final lower test at `z = 1`. -/
def lowerEnd (s : Seg) (e L : ℚ) : Bool := decide (L < evalQ s.G (1 - s.c) - e)

/-- Final upper test at `z = 1`. -/
def upperEnd (s : Seg) (e L : ℚ) : Bool := decide (evalQ s.G (1 - s.c) + e < L)

theorem lowerEnd_sound {k P : ℝ → ℝ} {s : Seg} {e E L : ℚ}
    (h : Inv k P s ((1 : ℚ) : ℝ) e E) (hc : lowerEnd s e L = true) : (L : ℝ) < k 1 := by
  unfold lowerEnd at hc
  rw [decide_eq_true_eq] at hc
  have h1 := h.1
  have hg : s.g ((1 : ℚ) : ℝ) = (evalQ s.G (1 - s.c) : ℝ) := evalR_rat _ _ _
  rw [hg] at h1
  have hL' : (L : ℝ) < (evalQ s.G (1 - s.c) : ℝ) - e := by exact_mod_cast hc
  push_cast at h1
  have := (abs_le.1 h1).1
  linarith

theorem upperEnd_sound {k P : ℝ → ℝ} {s : Seg} {e E L : ℚ}
    (h : Inv k P s ((1 : ℚ) : ℝ) e E) (hc : upperEnd s e L = true) : k 1 < L := by
  unfold upperEnd at hc
  rw [decide_eq_true_eq] at hc
  have h1 := h.1
  have hg : s.g ((1 : ℚ) : ℝ) = (evalQ s.G (1 - s.c) : ℝ) := evalR_rat _ _ _
  rw [hg] at h1
  have hL' : (evalQ s.G (1 - s.c) : ℝ) + e < L := by exact_mod_cast hc
  push_cast at h1
  have := (abs_le.1 h1).2
  linarith

end P241N


