-- Prove2me | Definitions.Def_Curvature_WeightedTrace
-- name    : Curvature_WeightedTrace
-- status  : Definition
-- author  : @ssakaue
-- created : 2026-11-24T07:11:46.477583+00:00
-- url     : https://prove2.me/theorems/f64268e7-d8f4-4953-b428-0fa144b456ab
-- title:
--   Signed initial cost, skipped creations and the weighted trace bound
-- statement:
--   This file defines the remaining quantities in the regret bound for a run of the general revocation update and proves that bound. Consider a run in $\mathbb R^N$ from a positive definite matrix $B$ and initial quadratic regularization terms with creation round $0$, value $0$, coefficient $\gamma\ge0$ and threshold $h>0$, with a parameter $\varepsilon\in(0,1]$ and creation thresholds $\zeta_t\ge0$. In round $t$, write $\widetilde g_t$ for the internal input, $z_t$ for the internal iterate, $H_t^-$ for the Hessian after the movement and $s_t^2\coloneqq\widetilde g_t^\top(H_t^-)^{-1}\widetilde g_t$, so that a term is created exactly when $s_t^2>\zeta_t$. Write $\lVert x\rVert_B^2\coloneqq x^\top Bx$.
--
--   For an initial term with direction $q$ and coefficient $\gamma$, an end point $z$ and a comparator $u$, the signed initial quantity is $\gamma\bigl(2\langle q,z\rangle\langle q,u\rangle-\langle q,z\rangle^2\bigr)$. The initial cost $\mathrm{Init}_T(u)$ sums this quantity over the revoked initial terms at their revocation points and over the surviving initial terms at the final iterate $z_{T+1}$. The skipped sum $\mathrm{Skip}_T$ adds $s_t^2$ over the rounds $t\le T$ with $s_t^2\le\zeta_t$, in which no term was created. With $r_t\coloneqq\langle\widetilde g_t,z_t-u\rangle$, the file proves for every comparator $u\in\mathbb R^N$ and horizon $T$ that
--
--   $$
--   2\sum_{t=1}^Tr_t-\varepsilon\sum_{t=1}^T|r_t|+\lVert u-z_{T+1}\rVert_B^2\le\lVert u\rVert_B^2+\mathrm{Init}_T(u)+\Bigl(1+\frac{\varepsilon^2}{48}\Bigr)\sum_as_a^2+\mathrm{Skip}_T,
--   $$
--
--   where $a$ runs over the created terms that survive after round $T$ and $s_a^2$ is the value of $s_t^2$ in the round that created $a$.
--
--   The sum over the surviving created terms is bounded by a trace. If every internal input has the form $A^\top g$ with $\lVert g\rVert_2\le1$, the file bounds $(1+\varepsilon^2/48)\sum_as_a^2$ by $c_\varepsilon\operatorname{tr}(A^\top AH^{-1})$, where $H$ is $B$ plus the curvature of the surviving initial terms, $c_\varepsilon$ depends only on $\varepsilon$, and $c_\varepsilon\le100/\varepsilon^2$. A fixed-matrix run starts from $\frac12x^\top Bx$ with no initial terms. If its inputs satisfy $S-\widetilde g_t\widetilde g_t^\top\succeq0$ for a positive semidefinite matrix $S$, the left-hand side above is at most $\lVert u\rVert_B^2+(100/\varepsilon^2)\operatorname{tr}(SB^{-1})+\sum_{t=1}^T\zeta_t$. These bounds are used in Appendices B.3–B.5 and for the fixed initialization of Appendix B.7.
-- source:
--   arXiv:2611.27572v1, Appendices B.3–B.5, pp. 35–39; Appendix B.7, pp. 40–42. https://arxiv.org/html/2611.27572v1#A2.SS4

import Definitions.Def_Curvature_GeneralRun
import Definitions.Def_Curvature_InitialCoordinates
import Definitions.Def_Curvature_Movement
import Mathlib.Analysis.Matrix.Order

section
set_option autoImplicit false
namespace Curvature

variable {d N : ℕ}

/-- The Gram matrix dominates the internal rank-one input for a unit-bounded ambient input. -/
theorem gram_sub_rankOne_posSemidef (A : Matrix (Fin d) (Fin N) ℝ) (g : Vec d)
    (hg : norm₂ g ≤ 1) :
    (A.transpose * A - Matrix.vecMulVec (A.transpose.mulVec g)
      (A.transpose.mulVec g)).PosSemidef := by
  have hgram : (A.transpose * A).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A
  let q := A.transpose.mulVec g
  have hq : (Matrix.vecMulVec q q).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star q
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hgram.isHermitian.sub hq.isHermitian)
    fun x => ?_
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, Matrix.vecMulVec_mulVec, dotProduct_smul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, dotProduct_comm g (A.mulVec x),
    ← norm₂_sq]
  have hdot := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g (A.mulVec x)
  have hsq : dotProduct g (A.mulVec x) ^ 2 ≤ norm₂ g ^ 2 * norm₂ (A.mulVec x) ^ 2 := by
    rw [norm₂_sq, norm₂_sq]
    simpa only [pow_two, dotProduct] using hdot
  apply sub_nonneg.mpr
  have hxq : dotProduct (A.transpose.mulVec g) x = dotProduct (A.mulVec x) g := by
    rw [dotProduct_comm (A.transpose.mulVec g), Matrix.dotProduct_transpose_mulVec,
      dotProduct_comm]
  rw [hxq, ← pow_two, dotProduct_comm (A.mulVec x) g]
  exact hsq.trans (by
    simpa only [one_pow, one_mul] using
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm₂_nonneg g) hg 2)
        (sq_nonneg (norm₂ (A.mulVec x))))

theorem trace_gram_mul_nonneg (A : Matrix (Fin d) (Fin N) ℝ) (H : Mat N)
    (hH : H.PosSemidef) : 0 ≤ (A.transpose * A * H).trace := by
  rw [← Matrix.trace_mul_cycle A H A.transpose]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (hH.mul_mul_conjTranspose_same A).trace_nonneg

theorem weightedTraceDrop_rankOne_eq (S H : Mat N) (hH : H.PosDef) (q : Vec N) (γ : ℝ)
    (hden : 1 + γ * dotProduct q (H⁻¹.mulVec q) ≠ 0) :
    let w := H⁻¹.mulVec q
    (S * H⁻¹).trace - (S * (H + γ • Matrix.vecMulVec q q)⁻¹).trace =
      γ * dotProduct w (S.mulVec w) / (1 + γ * dotProduct q w) := by
  dsimp only
  rw [inv_rankOne_add H hH q γ hden]
  simp only [mul_sub, Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul, sub_sub_cancel]
  rw [dotProduct_comm (S.mulVec (H⁻¹.mulVec q))]
  ring

theorem weightedTraceDrop_rankOne_ge (S H : Mat N) (hH : H.PosDef) (q : Vec N)
    (hq : (S - Matrix.vecMulVec q q).PosSemidef) (γ v τ : ℝ)
    (hv : 0 < v) (hvs : v ≤ dotProduct q (H⁻¹.mulVec q))
    (hτ : 0 < τ) (hweight : τ / 2 < γ * v) :
    (τ / (2 + τ)) * v ≤
      (S * H⁻¹).trace - (S * (H + γ • Matrix.vecMulVec q q)⁻¹).trace := by
  let w := H⁻¹.mulVec q
  let s := dotProduct q w
  have hs : 0 < s := hv.trans_le hvs
  have hγ : 0 < γ := pos_of_mul_pos_left ((half_pos hτ).trans hweight) hv.le
  have hγs : 0 < γ * s := mul_pos hγ hs
  have hpos : 0 < 1 + γ * s := by positivity
  have hquad : s ^ 2 ≤ dotProduct w (S.mulVec w) := by
    have hn := hq.dotProduct_mulVec_nonneg w
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.vecMulVec_mulVec,
      dotProduct_smul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, dotProduct_comm w q,
      ← pow_two] at hn
    exact sub_nonneg.mp hn
  have hratio : τ / (2 + τ) ≤ (γ * s) / (1 + γ * s) := by
    have hτs : τ / 2 ≤ γ * s := hweight.le.trans (mul_le_mul_of_nonneg_left hvs hγ.le)
    apply (div_le_div_iff₀ (by positivity) hpos).mpr
    linarith only [hτs]
  rw [weightedTraceDrop_rankOne_eq S H hH q γ hpos.ne']
  change (τ / (2 + τ)) * v ≤ γ * dotProduct w (S.mulVec w) / (1 + γ * s)
  calc
    _ ≤ ((γ * s) / (1 + γ * s)) * s :=
      mul_le_mul hratio hvs hv.le (div_nonneg hγs.le hpos.le)
    _ = γ * s ^ 2 / (1 + γ * s) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hquad hγ.le) hpos.le

theorem weightedSurvivorTraceSum_le_trace_drop (S B : Mat N) (hB : B.PosDef)
    (τ : ℝ) (hτ : 0 < τ) (survivors : List (Term N)) (measured : Term N → ℝ)
    (hstep : ∀ before a after, survivors = before ++ a :: after →
      let H := B + (before.map Term.curvature).sum
      (S - Matrix.vecMulVec a.q a.q).PosSemidef ∧
      0 < measured a ∧ τ / 2 < a.γ * measured a ∧
        measured a ≤ dotProduct a.q (H⁻¹.mulVec a.q)) :
    (τ / (2 + τ)) * (survivors.map measured).sum ≤
      (S * B⁻¹).trace - (S * (B + (survivors.map Term.curvature).sum)⁻¹).trace := by
  induction survivors generalizing B with
  | nil => simp
  | cons a after ih =>
    obtain ⟨hq, hv, hweight, hvs⟩ := hstep [] a after rfl
    simp only [List.map_nil, List.sum_nil, add_zero] at hvs
    have hγ := pos_of_mul_pos_left ((half_pos hτ).trans hweight) hv.le
    let B' := B + a.curvature
    have hB' : B'.PosDef := hB.add_posSemidef (a.curvature_posSemidef hγ.le)
    have hdrop : (τ / (2 + τ)) * measured a ≤
        (S * B⁻¹).trace - (S * B'⁻¹).trace := by
      simpa only [B', Term.curvature_eq_smul_vecMulVec] using
        weightedTraceDrop_rankOne_ge S B hB a.q hq a.γ (measured a) τ hv hvs hτ hweight
    have htail := ih B' hB' (by
      intro before entry suffix hsplit
      have hfull : a :: after = (a :: before) ++ entry :: suffix := by
        simp only [List.cons_append, hsplit]
      simpa only [B', List.map_cons, List.sum_cons, ← add_assoc] using
        hstep (a :: before) entry suffix hfull)
    simpa only [B', List.map_cons, List.sum_cons, mul_add, add_assoc,
      sub_add_sub_cancel] using add_le_add hdrop htail

theorem weightedSurvivorTraceSum (A : Matrix (Fin d) (Fin N) ℝ) (B : Mat N) (hB : B.PosDef)
    (τ : ℝ) (hτ : 0 < τ) (survivors : List (Term N)) (measured : Term N → ℝ)
    (hstep : ∀ before a after, survivors = before ++ a :: after →
      let H := B + (before.map Term.curvature).sum
      (A.transpose * A - Matrix.vecMulVec a.q a.q).PosSemidef ∧
      0 < measured a ∧ τ / 2 < a.γ * measured a ∧
        measured a ≤ dotProduct a.q (H⁻¹.mulVec a.q)) :
    (1 + τ) * (survivors.map measured).sum ≤
      ((1 + τ) * (2 + τ) / τ) * (A.transpose * A * B⁻¹).trace := by
  have hγ : ∀ a ∈ survivors, 0 ≤ a.γ := by
    intro a ha
    obtain ⟨before, after, hsplit⟩ := List.append_of_mem ha
    obtain ⟨_, hv, hweight, _⟩ := hstep before a after hsplit
    exact (pos_of_mul_pos_left ((half_pos hτ).trans hweight) hv.le).le
  have hH := hB.add_posSemidef (activeCurvature_posSemidef survivors hγ)
  have htrace := trace_gram_mul_nonneg A _ hH.inv.posSemidef
  have hbound := (weightedSurvivorTraceSum_le_trace_drop (A.transpose * A) B hB τ hτ
    survivors measured hstep).trans (sub_le_self _ htrace)
  have hpos : 0 < 2 + τ := by positivity
  have hsum : (survivors.map measured).sum ≤ (A.transpose * A * B⁻¹).trace / (τ / (2 + τ)) :=
    (le_div_iff₀ (div_pos hτ hpos)).mpr (by simpa only [mul_comm] using hbound)
  calc
    _ ≤ (1 + τ) * ((A.transpose * A * B⁻¹).trace / (τ / (2 + τ))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

theorem weightedTraceCoefficient_le {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1) :
    let τ := ε ^ 2 / 48
    (1 + τ) * (2 + τ) / τ ≤ 100 / ε ^ 2 := by
  dsimp only
  have hsq : ε ^ 2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hε.le hε' 2
  have hτ : ε ^ 2 / 48 ≤ 1 / 48 := div_le_div_of_nonneg_right hsq (by norm_num)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hprod : (1 + ε ^ 2 / 48) * (2 + ε ^ 2 / 48) ≤ 100 / 48 :=
    (mul_le_mul (show 1 + ε ^ 2 / 48 ≤ 1 + 1 / 48 by linarith)
      (show 2 + ε ^ 2 / 48 ≤ 2 + 1 / 48 by linarith) (by positivity) (by norm_num)).trans
      (by norm_num)
  calc
    _ ≤ (100 / 48) * ε ^ 2 := mul_le_mul_of_nonneg_right hprod (sq_nonneg ε)
    _ = _ := by ring

end Curvature

end

section
set_option autoImplicit false
namespace Curvature

variable {d N : ℕ}

theorem createdTerm_measuredWeight {ε : ℝ} (hε : 0 < ε)
    (round : ℕ) (q : Vec N) (moved : BallState N)
    (hs : 0 < dotProduct q (moved.hessian⁻¹.mulVec q)) :
    let a := createdTerm ε round q moved
    a.γ * a.measuredSquare ε = ε ^ 2 / 48 := by
  dsimp only
  rw [createdTerm_measuredSquare hε]
  change (ε ^ 2 / (48 * dotProduct q (moved.hessian⁻¹.mulVec q))) *
    dotProduct q (moved.hessian⁻¹.mulVec q) = _
  field_simp [hs.ne']

/-- Sum the measured squares for added terms, starting at the surviving initial curvature. -/
theorem weightedSurvivorTrace_of_provenance (A : Matrix (Fin d) (Fin N) ℝ)
    (B : Mat N) (hB : B.PosDef) {ε : ℝ} (hε : 0 < ε)
    (initial newest : List (Term N)) (hγ : ∀ a ∈ initial, 0 ≤ a.γ)
    (hprovenance : ∀ newer a older, newest = newer ++ a :: older →
      ∃ (k : ℕ) (g : Vec d) (moved : BallState N),
        let q := A.transpose.mulVec g
        norm₂ g ≤ 1 ∧ q ≠ 0 ∧ HessianInvariant B moved ∧
          a = createdTerm ε (k + 1) q moved ∧ (older ++ initial).Sublist moved.active) :
    let τ := ε ^ 2 / 48
    let residual := B + (initial.map Term.curvature).sum
    (1 + τ) * (newest.map fun a => a.measuredSquare ε).sum ≤
      ((1 + τ) * (2 + τ) / τ) * (A.transpose * A * residual⁻¹).trace := by
  let τ := ε ^ 2 / 48
  let residual := B + (initial.map Term.curvature).sum
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hresidual := hB.add_posSemidef (activeCurvature_posSemidef initial hγ)
  have hstep : ∀ before a after, newest.reverse = before ++ a :: after →
      let H := residual + (before.map Term.curvature).sum
      (A.transpose * A - Matrix.vecMulVec a.q a.q).PosSemidef ∧
      0 < a.measuredSquare ε ∧ τ / 2 < a.γ * a.measuredSquare ε ∧
        a.measuredSquare ε ≤ dotProduct a.q (H⁻¹.mulVec a.q) := by
    intro before a after hsplit
    have hnewest : newest = after.reverse ++ a :: before.reverse := by
      simpa only [List.reverse_reverse, List.reverse_append, List.reverse_cons,
        List.append_assoc, List.singleton_append] using congrArg List.reverse hsplit
    obtain ⟨k, g, moved, hg, hq, hM, ha, hold⟩ :=
      hprovenance after.reverse a before.reverse hnewest
    let q := A.transpose.mulVec g
    let H := residual + (before.map Term.curvature).sum
    have hsq : a.measuredSquare ε = dotProduct q (moved.hessian⁻¹.mulVec q) := by
      rw [ha, createdTerm_measuredSquare hε]
    have hspos : 0 < dotProduct q (moved.hessian⁻¹.mulVec q) :=
      hM.inverseDirection_pos hB hq
    have hH : H.PosDef := by
      have hγbefore : ∀ b ∈ before, 0 ≤ b.γ := by
        intro b hb
        exact hM.gamma_nonneg b
          (hold.subset (List.mem_append_left initial (List.mem_reverse.mpr hb)))
      exact hresidual.add_posSemidef (activeCurvature_posSemidef before hγbefore)
    have hdiff : (moved.hessian - H).PosSemidef := by
      have hsum := activeCurvature_sublist_difference_posSemidef hold hM.gamma_nonneg
      simpa only [H, residual, hM.decomposition, add_assoc, add_comm _ (initial.map _).sum,
        add_sub_add_left_eq_sub, List.map_append, List.sum_append, List.map_reverse,
        List.sum_reverse] using hsum
    refine ⟨?_, hsq.symm ▸ hspos, ?_, ?_⟩
    · rw [ha]
      exact gram_sub_rankOne_posSemidef A g hg
    · rw [ha, createdTerm_measuredWeight hε _ _ _ hspos]
      change τ / 2 < τ
      exact half_lt_self hτ
    · rw [hsq, ha]
      exact inverseQuadratic_mono hH (hM.posDef hB) hdiff q
  simpa only [List.map_reverse, List.sum_reverse] using
    weightedSurvivorTraceSum A residual hresidual τ hτ newest.reverse
      (fun a => a.measuredSquare ε) hstep

section Run

variable {B : Mat N} {I : List (Term N)} {ε : ℝ} {ζ : ℕ → ℝ}
  {feed : ℕ → Vec N → Vec N}

local notation "s" => generalStateAfter (generalInitial B I) ε ζ feed
local notation "q" => (fun k => feed k (BallState.z (s k)))

private theorem generalStateAfter_initialLast (hB : B.PosDef) (hI : GeneralInitialTerms I)
    (hε : 0 < ε) (hζ : ∀ i, 0 ≤ ζ i) (t : ℕ) :
    (s t).active.Pairwise (fun a b => a.round = 0 → b.round = 0) := by
  induction t with
  | zero =>
    exact List.pairwise_iff_getElem.mpr fun _ j _ hj _ _ =>
      hI.initialRound I[j] (List.getElem_mem hj)
  | succ t ih =>
    obtain ⟨hH, hInt⟩ := generalStateAfter_invariant hB hI hε hζ feed t
    obtain ⟨removed, hist⟩ := moveLoop_history _ _ _ _ _ hInt
      (generalMove_spec hB hH hInt (q t)).1
    have ht := List.Pairwise.sublist hist.survivors ih
    change (generalStep ε (ζ t) (t + 1) (s t) (q t)).active.Pairwise _
    unfold generalStep
    split
    · exact List.pairwise_cons.mpr ⟨fun _ _ h => (Nat.succ_ne_zero t h).elim, ht⟩
    · exact ht

private theorem initialLast_filter_append {l : List (Term N)}
    (h : l.Pairwise (fun a b => a.round = 0 → b.round = 0)) :
    l = l.filter (fun a => decide (a.round ≠ 0)) ++ l.filter (fun a => decide (a.round = 0)) := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
    by_cases ha : a.round = 0
    · have hnew : tail.filter (fun b => decide (b.round ≠ 0)) = [] :=
        List.filter_eq_nil_iff.mpr fun b hb => by simp [hhead b hb ha]
      have hold : tail.filter (fun b => decide (b.round = 0)) = tail :=
        List.filter_eq_self.mpr fun b hb => by simp [hhead b hb ha]
      have hnewCons : (a :: tail).filter (fun b => decide (b.round ≠ 0)) = [] := by
        rw [List.filter_cons_of_neg (p := fun b : Term N => decide (b.round ≠ 0)) (by simp [ha])]
        exact hnew
      have holdCons : (a :: tail).filter (fun b => decide (b.round = 0)) = a :: tail := by
        rw [List.filter_cons_of_pos (p := fun b : Term N => decide (b.round = 0))
          (decide_eq_true ha), hold]
      rw [hnewCons, holdCons, List.nil_append]
    · rw [List.filter_cons_of_pos (p := fun b : Term N => decide (b.round ≠ 0))
        (decide_eq_true ha),
        List.filter_cons_of_neg (p := fun b : Term N => decide (b.round = 0)) (by simp [ha]),
        List.cons_append]
      exact congrArg (List.cons a) (ih htail)

theorem generalStateAfter_activePartition (hB : B.PosDef) (hI : GeneralInitialTerms I)
    (hε : 0 < ε) (hζ : ∀ i, 0 ≤ ζ i) (t : ℕ) :
    (s t).active = (s t).active.filter (fun a => decide (a.round ≠ 0)) ++
      (s t).active.filter (fun a => decide (a.round = 0)) :=
  initialLast_filter_append (generalStateAfter_initialLast hB hI hε hζ t)

theorem generalStateAfter_survivor_provenance (hB : B.PosDef) (hI : GeneralInitialTerms I)
    (hε : 0 < ε) (hζ : ∀ i, 0 ≤ ζ i) (t : ℕ)
    (a : Term N) (older : List (Term N)) (ha : a.round ≠ 0)
    (hsub : (a :: older).Sublist (s t).active) :
    ∃ k < t,
      let moved := generalMove (s k) (q k)
      q k ≠ 0 ∧ HessianInvariant B moved ∧
        a = createdTerm ε (k + 1) (q k) moved ∧ older.Sublist moved.active := by
  induction t with
  | zero =>
    exact (ha (hI.initialRound a (List.mem_of_cons_sublist hsub))).elim
  | succ t ih =>
    obtain ⟨hH, hInt⟩ := generalStateAfter_invariant hB hI hε hζ feed t
    let moved := generalMove (s t) (q t)
    obtain ⟨hm, hM, _⟩ := generalMove_spec hB hH hInt (q t)
    obtain ⟨removed, hist⟩ := moveLoop_history _ _ _ _ _ hInt hm
    change (a :: older).Sublist (generalStep ε (ζ t) (t + 1) (s t) (q t)).active at hsub
    by_cases hadd : ζ t < generalSquare (s t) (q t)
    · simp only [generalStep, if_pos hadd, BallState.addTerm] at hsub
      rcases List.cons_sublist_cons'.mp hsub with hskip | ⟨heq, hold⟩
      · obtain ⟨k, hk, hcreation⟩ := ih (hskip.trans hist.survivors)
        exact ⟨k, Nat.lt_succ_of_lt hk, hcreation⟩
      · have hq : q t ≠ 0 := by
          intro hzero
          have hpositive := (hζ t).trans_lt hadd
          simp [generalSquare, hzero] at hpositive
        exact ⟨t, Nat.lt_succ_self t, hq, hM, heq, hold⟩
    · simp only [generalStep, if_neg hadd] at hsub
      obtain ⟨k, hk, hcreation⟩ := ih (hsub.trans hist.survivors)
      exact ⟨k, Nat.lt_succ_of_lt hk, hcreation⟩

end Run

/-- The weighted trace bound for the actual run with internal inputs obtained from a coordinate map. -/
theorem weightedSurvivorTraceOnRun (A : Matrix (Fin d) (Fin N) ℝ) {B : Mat N}
    (hB : B.PosDef) {I : List (Term N)} (hI : GeneralInitialTerms I)
    {ε : ℝ} (hε : 0 < ε) {ζ : ℕ → ℝ} (hζ : ∀ i, 0 ≤ ζ i)
    (ambient : ℕ → Vec N → Vec d) (hnorm : ∀ k z, norm₂ (ambient k z) ≤ 1) (t : ℕ) :
    let s := generalStateAfter (generalInitial B I) ε ζ (fun k z => A.transpose.mulVec (ambient k z))
    let initial := (s t).active.filter (fun a => decide (a.round = 0))
    let newest := (s t).active.filter (fun a => decide (a.round ≠ 0))
    let τ := ε ^ 2 / 48
    let residual := B + (initial.map Term.curvature).sum
    (1 + τ) * (newest.map fun a => a.measuredSquare ε).sum ≤
      ((1 + τ) * (2 + τ) / τ) * (A.transpose * A * residual⁻¹).trace := by
  let feed := fun k z => A.transpose.mulVec (ambient k z)
  let s := generalStateAfter (generalInitial B I) ε ζ feed
  let initial := (s t).active.filter (fun a => decide (a.round = 0))
  let newest := (s t).active.filter (fun a => decide (a.round ≠ 0))
  have hH := (generalStateAfter_invariant hB hI hε hζ feed t).1
  have hγ : ∀ a ∈ initial, 0 ≤ a.γ := fun a ha =>
    hH.gamma_nonneg a (List.mem_filter.mp ha).1
  apply weightedSurvivorTrace_of_provenance A B hB hε initial newest hγ
  intro newer a older hsplit
  have hactive : (s t).active = newer ++ a :: (older ++ initial) := by
    rw [show (s t).active = newest ++ initial from
      generalStateAfter_activePartition (feed := feed) hB hI hε hζ t,
      hsplit, List.append_assoc, List.cons_append]
  have ha : a.round ≠ 0 := by
    have hmem : a ∈ newest := hsplit ▸ List.mem_append_right _ List.mem_cons_self
    exact of_decide_eq_true (List.mem_filter.mp hmem).2
  have hsub : (a :: (older ++ initial)).Sublist (s t).active := by
    rw [hactive]
    exact List.sublist_append_right _ _
  obtain ⟨k, _, hq, hM, hcreation, hold⟩ :=
    generalStateAfter_survivor_provenance (feed := feed) hB hI hε hζ t a _ ha hsub
  exact ⟨k, ambient k (s k).z, _, hnorm k (s k).z, hq, hM, hcreation, hold⟩

end Curvature

end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}

def generalInitialResidual (a : Term d) (z u : Vec d) : ℝ :=
  a.γ * (2 * dotProduct a.q z * dotProduct a.q u - (dotProduct a.q z)^2)

def generalInitialCost (removed : List (Term d × Vec d)) (active : List (Term d))
    (z u : Vec d) : ℝ :=
  ((generalInitialRemoved removed).map fun e => generalInitialResidual e.1 e.2 u).sum +
    ((generalInitialSurvivors active).map fun a => generalInitialResidual a z u).sum

def generalSkippedSum (ζ : ℕ → ℝ) (s : ℕ → BallState d) (q : ℕ → Vec d) (T : ℕ) : ℝ :=
  ∑ i ∈ Finset.range T, if ζ i < generalSquare (s i) (q i) then 0 else generalSquare (s i) (q i)

theorem generalSkipTail (L : ℝ) (hL : 0 ≤ L) (T : ℕ) :
    (∑ i ∈ Finset.range T, L / ((i : ℝ) + 2)^4) ≤
      L / 8 * (1 - 1 / ((T : ℝ) + 1)) := by
  induction T with
  | zero => simp
  | succ t ih =>
    have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
    have hdiff : L / ((t : ℝ)+2)^4 ≤ L / 8 * (1/((t : ℝ)+1) - 1/((t : ℝ)+2)) := by
      field_simp
      nlinarith [mul_nonneg hL (sq_nonneg (t : ℝ)), mul_nonneg hL ht,
        mul_nonneg hL (pow_nonneg ht 3)]
    rw [Finset.sum_range_succ, Nat.cast_succ]
    rw [show (t : ℝ)+1+1 = (t : ℝ)+2 by ring]
    linarith only [ih, hdiff]

theorem generalSkipBudget_le (L : ℝ) (hL : 0 ≤ L) (s : ℕ → BallState d) (q : ℕ → Vec d)
    (T : ℕ) : generalSkippedSum (fun i => L / ((i : ℝ) + 2)^4) s q T ≤
      L / 8 * (1 - 1 / ((T : ℝ) + 1)) := by
  apply le_trans _ (generalSkipTail L hL T)
  apply Finset.sum_le_sum
  intro i hi
  split
  · positivity
  · exact le_of_not_gt ‹_›


theorem generalInitialResidual_eq {a : Term d} (hm : a.m = 0) (z u : Vec d) :
    2 * a.value u = 2 * a.divergence u z + generalInitialResidual a z u := by
  simp [Term.value, Term.residual, Term.divergence, generalInitialResidual, hm, dotProduct_sub]
  ring

private theorem sumFilter {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) :
    (l.map fun a => if p a then f a else 0).sum =
      ((l.filter fun a => decide (p a)).map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

private theorem generalFtrlIdentity (s : ℕ → BallState d) (q : ℕ → Vec d)
    (hz : (s 0).regularizer (s 0).z = 0) (u : Vec d) (T : ℕ) :
    (∑ t ∈ Finset.range T, excess (q t) (s t).z u) =
      (s T).regularizer u + (∑ t ∈ Finset.range T, roundStability s q t) -
        (ftrlObjective s q T u - ftrlObjective s q T (s T).z) := by
  have ht : (∑ t ∈ Finset.range T, roundStability s q t) =
      (∑ t ∈ Finset.range T, dotProduct (q t) (s t).z) - ftrlObjective s q T (s T).z := by
    induction T with
    | zero => simp [ftrlObjective, hz]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      unfold roundStability
      ring
  rw [ht]
  simp only [excess, dotProduct_sub, Finset.sum_sub_distrib, ftrlObjective]
  ring

section Run
variable {B : Mat d} {I : List (Term d)} {ε : ℝ} {ζ : ℕ → ℝ} {feed : ℕ → Vec d → Vec d}
local notation "s" => generalStateAfter (generalInitial B I) ε ζ feed
local notation "q" => (fun i => feed i (BallState.z (s i)))

private theorem generalLifetime_created (hB : B.PosDef) (hI : GeneralInitialTerms I)
    (hε : 0 < ε) (hε' : ε ≤ 1) (hζ : ∀ i, 0 ≤ ζ i) (i : ℕ)
    (hadd : ζ i < generalSquare (s i) (q i)) (ending u : Vec d) (revoked : Bool)
    (a : Term d) (ha : a = createdTerm ε (i+1) (q i) (generalMove (s i) (q i)))
    (hend : |a.residual ending| < 3 * a.h) (hhit : revoked = true → a.h ≤ |a.residual ending|) :
    2 * a.value u + (2 * roundStability s q (a.round-1) -
      ε * |excess (q (a.round-1)) (s (a.round-1)).z u|) ≤ 2 * a.divergence u ending +
      (if revoked then 0 else (1+ε^2/48)*a.measuredSquare ε) := by
  let V := generalSquare (s i) (q i)
  have hv : 0 < V := (hζ i).trans_lt hadd
  obtain ⟨hS, hδ⟩ := generalRound_energy (feed := feed) hB hI hε hζ i
  have hr : a.round = i+1 := by rw [ha]; rfl
  have hh : a.h = 8*V/ε := by rw [ha]; rfl
  have hq : a.q = q i := by rw [ha]; rfl
  have hcenter : a.m = dotProduct a.q (s (i+1)).z := by
    rw [ha]
    change _ = dotProduct _ (generalStep ε (ζ i) (i+1) (s i) (q i)).z
    rw [generalStep_z]
    rfl
  have hcoeff : a.γ = ε^2/(48*V) := by rw [ha]; rfl
  have he := termLifetimeBound a (s i).z (s (i+1)).z ending u ε V (roundStability s q i)
    revoked hε hε' hv hcenter hcoeff (hq ▸ hδ.1) (hq ▸ hδ.2) hS.2 (hh ▸ hend.le) (hh ▸ hhit)
  have hmass : a.measuredSquare ε = V := ha ▸ createdTerm_measuredSquare hε _ _ _
  rw [hr, Nat.add_one_sub_one, hmass]
  rw [hq] at he
  cases revoked <;> simp only [Bool.false_eq_true, if_false, if_true] at he ⊢ <;> linarith

theorem generalLifetimeOnRun (hB : B.PosDef) (hI : GeneralInitialTerms I)
    (hε : 0 < ε) (hε' : ε ≤ 1) (hζ : ∀ i, 0 ≤ ζ i) (T : ℕ) (u : Vec d)
    {removed : List (Term d × Vec d)} (hist : GeneralRunHistory I ε ζ s q T removed) :
    let r := fun i => excess (q i) (s i).z u
    let v := u - (s T).z
    2 * (∑ i ∈ Finset.range T, r i) - ε * (∑ i ∈ Finset.range T, |r i|) +
      dotProduct v (B.mulVec v) ≤ dotProduct u (B.mulVec u) +
        generalInitialCost removed (s T).active (s T).z u +
        (1 + ε ^ 2 / 48) * ((generalAddedSurvivors (s T).active).map fun a => a.measuredSquare ε).sum +
        generalSkippedSum ζ s q T := by
  let r := fun i => excess (q i) (s i).z u
  let w := fun i => 2 * roundStability s q i - ε * |r i|
  let score := fun a : Term d => 2*a.value u + if a.round=0 then 0 else w (a.round-1)
  let c := 1 + ε^2/48
  let mass := fun a : Term d => a.measuredSquare ε
  let init := fun a : Term d => fun z => if a.round=0 then generalInitialResidual a z u else 0
  let extra := fun a : Term d => if a.round≠0 then c * mass a else 0
  let A := generalAdditions ε ζ s q T
  have point : ∀ a ∈ A ++ I, ∀ z (rev : Bool), |a.residual z| < 3*a.h →
      (rev = true → a.h ≤ |a.residual z|) →
      score a ≤ 2*a.divergence u z + init a z + (if rev then 0 else extra a) := by
    intro a ha z rev hend hhit
    rcases List.mem_append.mp ha with hadded | hinitial
    · have hn := generalAdditions_positive_round hadded
      obtain ⟨i, _, hi, ha⟩ := generalAdditions_origin hadded
      simpa [score, w, r, init, extra, hn, mass, c] using
        generalLifetime_created hB hI hε hε' hζ i hi z u rev a ha hend hhit
    · have hz := hI.initialRound a hinitial
      have he := generalInitialResidual_eq (hI.center a hinitial) z u
      cases rev <;> simp [score, init, extra, hz, he]
  have hrem : (removed.map fun e => score e.1).sum ≤
      2*(removed.map fun e => e.1.divergence u e.2).sum +
        ((generalInitialRemoved removed).map fun e => generalInitialResidual e.1 e.2 u).sum := by
    unfold generalInitialRemoved
    rw [← List.sum_map_mul_left, ← sumFilter removed (fun e => e.1.round = 0), ← List.sum_map_add]
    apply List.sum_le_sum
    rintro ⟨a,z⟩ ha
    have hm := hist.partition.mem_iff.mp (List.mem_append_left _ (List.mem_map.mpr ⟨_, ha, rfl⟩))
    obtain ⟨hlo, hhi⟩ := hist.thresholds _ _ ha
    simpa [init] using point a hm z true hhi (fun _ => hlo)
  have halive : ((s T).active.map score).sum ≤
      2*((s T).active.map fun a => a.divergence u (s T).z).sum +
      ((generalInitialSurvivors (s T).active).map fun a => generalInitialResidual a (s T).z u).sum +
      c*((generalAddedSurvivors (s T).active).map mass).sum := by
    unfold generalInitialSurvivors generalAddedSurvivors
    rw [← List.sum_map_mul_left, ← List.sum_map_mul_left,
      ← sumFilter (s T).active (fun a => a.round = 0),
      ← sumFilter (s T).active (fun a => a.round ≠ 0), ← List.sum_map_add, ← List.sum_map_add]
    apply List.sum_le_sum
    intro a ha
    have hm := hist.partition.mem_iff.mp (List.mem_append_right _ ha)
    have hi := hist.interior a ha
    have hend : |a.residual (s T).z| < 3*a.h := by linarith [abs_nonneg (a.residual (s T).z)]
    simpa [init, extra] using point a hm (s T).z false hend (by simp)
  have hperm := (hist.partition.map score).sum_eq
  simp only [List.map_append, List.map_map, Function.comp_def, List.sum_append] at hperm
  have hA : (A.map score).sum = 2*(A.map fun a => a.value u).sum +
      ∑ i ∈ Finset.range T, if ζ i < generalSquare (s i) (q i) then w i else 0 := by
    rw [← generalAdditions_sum, ← List.sum_map_mul_left, ← List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    simp [score, generalAdditions_positive_round ha]
  have hinit : (I.map score).sum = 2*(I.map fun a => a.value u).sum := by
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    simp [score, hI.initialRound a ha]
  have hskip : (∑ i ∈ Finset.range T, w i) ≤
      (∑ i ∈ Finset.range T, if ζ i < generalSquare (s i) (q i) then w i else 0) +
      generalSkippedSum ζ s q T := by
    rw [generalSkippedSum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    split
    · simp
    · have he := (generalRound_energy (feed := feed) hB hI hε hζ i).1.2
      dsimp [w]
      linarith [mul_nonneg hε.le (abs_nonneg (r i))]
  dsimp only [w] at hskip
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hskip
  have hreg := hist.regularizer u
  change _ = dotProduct u (B.mulVec u)/2 + (I.map fun a => a.value u).sum +
    (A.map fun a => a.value u).sum - _ at hreg
  have hid := generalFtrlIdentity s q (generalInitial_value_zero hI B) u T
  have hgap := generalStateAfter_gap (feed := feed) hB hI hε hζ T u
  change (∑ i ∈ Finset.range T, r i) = _ at hid
  change _ + _ = (A.map score).sum + _ at hperm
  rw [hA, hinit] at hperm
  change 2*(∑ i ∈ Finset.range T, r i) - ε*(∑ i ∈ Finset.range T, |r i|) + _ ≤
    _ + (_ + _) + c*((generalAddedSurvivors (s T).active).map mass).sum + _
  linarith only [hrem, halive, hperm, hskip, hreg, hid, hgap]

end Run
end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {N : ℕ}

theorem emptyGeneralInitialTerms : GeneralInitialTerms ([] : List (Term N)) := by
  constructor <;> simp

def fixedRun (B : Mat N) (ε : ℝ) (ζ : ℕ → ℝ) (feed : ℕ → Vec N → Vec N) :=
  generalStateAfter (generalInitial B []) ε ζ feed

private theorem gramFactor {S : Mat N} (hS : S.PosSemidef) : ∃ A : Mat N, S = A.transpose*A := by
  open scoped MatrixOrder in
  obtain ⟨A, ha⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hS.nonneg
  exact ⟨A, by simpa [Matrix.star_eq_conjTranspose] using ha⟩

theorem fixedInitialization (B S : Mat N) (hB : B.PosDef) (hS : S.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1) (ζ : ℕ → ℝ) (hζ : ∀ i, 0 ≤ ζ i)
    (feed : ℕ → Vec N → Vec N)
    (hq : ∀ i, let q := feed i (fixedRun B ε ζ feed i).z
               (S - Matrix.vecMulVec q q).PosSemidef)
    (u : Vec N) (T : ℕ) :
    let s := fixedRun B ε ζ feed
    let r := fun i => excess (feed i (s i).z) (s i).z u
    let v := u - (s T).z
    2*(∑ i ∈ Finset.range T, r i) - ε*(∑ i ∈ Finset.range T, |r i|) +
      dotProduct v (B.mulVec v) ≤ dotProduct u (B.mulVec u) +
      (100/ε^2)*(S*B⁻¹).trace + ∑ i ∈ Finset.range T, ζ i := by
  let s := fixedRun B ε ζ feed
  let q := fun i => feed i (s i).z
  let τ := ε^2/48
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨removed, hist⟩ := generalStateAfter_history (feed := feed) hB emptyGeneralInitialTerms hε hζ T
  have hp : (generalInitialRemoved removed).map Prod.fst ++ generalInitialSurvivors (s T).active = [] :=
    List.Perm.eq_nil (hist.initialPartition emptyGeneralInitialTerms)
  obtain ⟨hr, hs⟩ := List.append_eq_nil_iff.mp hp
  have hr' := List.map_eq_nil_iff.mp hr
  have hcost : generalInitialCost removed (s T).active (s T).z u = 0 := by
    simp [generalInitialCost, hr', hs]
  have hnew : generalAddedSurvivors (s T).active = (s T).active := by
    have h := generalStateAfter_activePartition (feed := feed) hB emptyGeneralInitialTerms hε hζ T
    change (s T).active = generalAddedSurvivors (s T).active ++ generalInitialSurvivors (s T).active at h
    simpa [hs] using h.symm
  obtain ⟨A,hA⟩ := gramFactor hS
  have hstep : ∀ before a after, (s T).active.reverse = before ++ a :: after →
      let H := B + (before.map Term.curvature).sum
      (A.transpose*A - Matrix.vecMulVec a.q a.q).PosSemidef ∧ 0 < a.measuredSquare ε ∧
        τ/2 < a.γ*a.measuredSquare ε ∧ a.measuredSquare ε ≤ dotProduct a.q (H⁻¹.mulVec a.q) := by
    intro before a after hsplit
    have hactive : (s T).active = after.reverse ++ a :: before.reverse := by
      simpa only [List.reverse_reverse, List.reverse_append, List.reverse_cons,
        List.append_assoc, List.singleton_append] using congrArg List.reverse hsplit
    have hsub : (a :: before.reverse).Sublist (s T).active :=
      hactive ▸ List.sublist_append_right _ _
    have hmem := List.mem_of_cons_sublist hsub
    rw [← hnew] at hmem
    have ha : a.round ≠ 0 := of_decide_eq_true (List.mem_filter.mp hmem).2
    obtain ⟨i, hi, hn, hM, heq, hold⟩ := generalStateAfter_survivor_provenance
      (feed := feed) hB emptyGeneralInitialTerms hε hζ T a before.reverse ha hsub
    let moved := generalMove (s i) (q i)
    have hv : 0 < dotProduct (q i) (moved.hessian⁻¹.mulVec (q i)) := hM.inverseDirection_pos hB hn
    let H := B + (before.map Term.curvature).sum
    have hH : H.PosDef := hB.add_posSemidef (activeCurvature_posSemidef before
      fun b hb => hM.gamma_nonneg b (hold.subset (List.mem_reverse.mpr hb)))
    have hdiff : (moved.hessian-H).PosSemidef := by
      simpa only [H, hM.decomposition, add_sub_add_left_eq_sub, List.map_reverse, List.sum_reverse,
        moved, q, s, fixedRun] using activeCurvature_sublist_difference_posSemidef hold hM.gamma_nonneg
    rw [heq]
    refine ⟨hA ▸ hq i, ?_, ?_, ?_⟩
    · rw [createdTerm_measuredSquare hε]
      exact hv
    · change τ/2 < (createdTerm ε (i+1) (q i) moved).γ * (createdTerm ε (i+1) (q i) moved).measuredSquare ε
      rw [createdTerm_measuredWeight hε _ _ _ hv]
      exact half_lt_self hτ
    · rw [createdTerm_measuredSquare hε]
      exact inverseQuadratic_mono hH (hM.posDef hB) hdiff (q i)
  have htrace := weightedSurvivorTraceSum A B hB τ hτ (s T).active.reverse
    (fun a => a.measuredSquare ε) hstep
  simp only [List.map_reverse, List.sum_reverse] at htrace
  rw [← hA] at htrace
  have hnonneg : 0 ≤ (S*B⁻¹).trace := hA ▸ trace_gram_mul_nonneg A _ hB.inv.posSemidef
  have hcoef := mul_le_mul_of_nonneg_right (weightedTraceCoefficient_le hε hε') hnonneg
  have hskip : generalSkippedSum ζ s q T ≤ ∑ i ∈ Finset.range T, ζ i := by
    apply Finset.sum_le_sum
    intro i hi
    split
    · exact hζ i
    · exact le_of_not_gt ‹_›
  have hl := generalLifetimeOnRun (feed := feed) hB emptyGeneralInitialTerms hε hε' hζ T u hist
  change _ ≤ dotProduct u (B.mulVec u) + generalInitialCost removed (s T).active (s T).z u +
    (1+τ)*((generalAddedSurvivors (s T).active).map (fun a => a.measuredSquare ε)).sum + generalSkippedSum ζ s q T at hl
  rw [hcost, add_zero, hnew] at hl
  exact hl.trans (add_le_add (add_le_add le_rfl (htrace.trans hcoef)) hskip)

end Curvature

end
end


