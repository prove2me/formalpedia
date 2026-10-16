-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
-- name    : OAI_Analysis_LipschitzFree_Coefficients
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T11:53:09.177762+00:00
-- url     : https://prove2.me/theorems/e14dce82-d38a-4716-bb79-0ed57d506237
-- title:
--   Coefficient isomorphism $\ell^1(\iota)\cong\mathcal{F}(M)$ for bounded 1-separated pointed metric spaces
-- statement:
--   Let $(M,d)$ be a metric space with base point $o$ and let $\mathcal{F}(M)$ be its Lipschitz-free space: the closed linear span, in the dual of the space $\mathrm{Lip}_0(M)$ of real Lipschitz functions vanishing at $o$ (normed by the best Lipschitz constant), of the evaluation functionals $\delta_x(f)=f(x)$. Assume that $M$ is **1-separated**, i.e. $d(x,y)\ge1$ whenever $x\neq y$, and for $j\in M$ let $c_j:\mathcal{F}(M)\to\mathbb{R}$ be the coordinate functional obtained by pairing with the indicator function of $\{j\}$ (taken to be $0$ when $j=o$), so that $c_j(\delta_x)=1$ if $x=j\neq o$ and $c_j(\delta_x)=0$ otherwise. Fix an index set $\iota$ and a bijection $e:\iota\to M\setminus\{o\}$, and let $\ell^1(\iota)$ be the real Banach space of absolutely summable families $c=(c_i)_{i\in\iota}$ with norm $\|c\|_1=\sum_{i\in\iota}|c_i|$.
--
--   1. **Analysis map.** $A:\mathcal{F}(M)\to\ell^1(\iota)$, $A(u)=\bigl(c_{e(i)}(u)\bigr)_{i\in\iota}$. Every finite partial sum of $|c_{e(i)}(u)|$ is at most $2\|u\|$, so $A(u)\in\ell^1(\iota)$, and $A$ is a bounded linear operator with $\|A(u)\|_1\le 2\|u\|$. It maps $\delta_{e(i)}$ to the $i$-th unit vector.
--
--   2. **Synthesis map.** Assume in addition that $d(x,o)\le B$ for all $x\in M$, for some real constant $B$. Then for each $c\in\ell^1(\iota)$ the series below converges absolutely in $\mathcal{F}(M)$ (its $i$-th term has norm at most $|c_i|\,B$), and
--   $$S(c)=\sum_{i\in\iota}c_i\,\delta_{e(i)}$$
--   defines a bounded linear operator $S:\ell^1(\iota)\to\mathcal{F}(M)$ with $\|S(c)\|\le B\,\|c\|_1$. It maps $r$ times the $i$-th unit vector to $r\,\delta_{e(i)}$.
--
--   3. **Isomorphism.** Under both hypotheses, $A\circ S$ is the identity of $\ell^1(\iota)$ and $S\circ A$ is the identity of $\mathcal{F}(M)$. Hence $S$ is an isomorphism of Banach spaces (a linear homeomorphism) from $\ell^1(\iota)$ onto $\mathcal{F}(M)$ with inverse $A$, and consequently
--   $$\tfrac12\,\|c\|_1\;\le\;\Bigl\|\sum_{i\in\iota}c_i\,\delta_{e(i)}\Bigr\|_{\mathcal{F}(M)}\;\le\;B\,\|c\|_1\qquad\text{for all } c\in\ell^1(\iota).$$
--
--   Transporting the norm of $\mathcal{F}(M)$ to $\ell^1$ through this isomorphism (with $\iota=\mathbb{N}$ for a countably infinite $M$) yields an equivalent norm on the sequence space $\ell^1$ with equivalence constants $\tfrac12$ and $B$; this is how renormings of $\ell^1$ are produced from bounded, uniformly discrete metric spaces.
--
--   **Formalization Note** `Coefficients.L1 ι` abbreviates `lp (fun _ : ι => ℝ) 1`, and `norm_eq_tsum`, `summable_abs` express its norm as $\sum_i|c_i|$. `analysis` and `synthesis` are the continuous linear maps of items 1 and 2 (built from `analysisLinear` and `synthesisLinear` with the bounds `analysis_bound`, `synthesis_bound`), the series is an unconditional sum (`tsum`), and `equiv` is the continuous linear equivalence of item 3 whose forward map is $S$. The 1-separation hypothesis `sep` is needed only for $A$ and the bound hypothesis `hb` only for $S$; nonnegativity of $B$ is automatic from $d(o,o)=0\le B$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Coefficients.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Coefficients.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming

namespace OAI

/-!
# Absolutely summable coefficients of bounded separated Lipschitz-free spaces
-/

noncomputable section
open scoped BigOperators ENNReal Classical

namespace DiscreteFree

namespace Coefficients

variable {ι M : Type*} [MetricSpace M] (o : M)
variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)
variable (e : ι ≃ {x : M // x ≠ o})

abbrev L1 (ι : Type*) := lp (fun _ : ι => ℝ) (1 : ENNReal)

theorem norm_eq_tsum (c : L1 ι) : ‖c‖ = ∑' i, |c i| := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal) c

theorem summable_abs (c : L1 ι) : Summable (fun i => |c i|) := by
  simpa using (lp.memℓp c).summable (by norm_num : 0 < (1 : ENNReal).toReal)

theorem sum_abs_le (u : FreeSpace o) (s : Finset ι) :
    ∑ i ∈ s, |coordinate o sep (e i).val u| ≤ 2 * ‖u‖ := by
  let j : ι ↪ M := e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  simpa only [Finset.sum_map, j, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Function.Embedding.coeFn_mk] using sum_abs_coordinate_le o sep (s.map j) u

def analysisLinear : FreeSpace o →ₗ[ℝ] L1 ι where
  toFun u := ⟨fun i => coordinate o sep (e i).val u, memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      summable_of_sum_le (fun i => abs_nonneg (coordinate o sep (e i).val u))
        (sum_abs_le o sep e u))⟩
  map_add' u v := by apply lp.ext; funext i; exact map_add _ u v
  map_smul' r u := by apply lp.ext; funext i; exact map_smul _ r u

@[simp] theorem analysisLinear_apply (u : FreeSpace o) (i : ι) :
    analysisLinear o sep e u i = coordinate o sep (e i).val u := rfl

theorem analysis_bound (u : FreeSpace o) : ‖analysisLinear o sep e u‖ ≤ 2 * ‖u‖ := by
  rw [norm_eq_tsum]
  exact Real.tsum_le_of_sum_le (fun i => abs_nonneg _) (sum_abs_le o sep e u)

def analysis : FreeSpace o →L[ℝ] L1 ι :=
  (analysisLinear o sep e).mkContinuous 2 (analysis_bound o sep e)

@[simp] theorem analysis_apply (u : FreeSpace o) (i : ι) :
    analysis o sep e u i = coordinate o sep (e i).val u := rfl

variable (B : ℝ) (hb : ∀ x, dist x o ≤ B)
include hb

theorem term_bound (c : L1 ι) (i : ι) :
    ‖c i • delta o (e i).val‖ ≤ |c i| * B := by
  rw [norm_smul, Real.norm_eq_abs, delta_norm]
  exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)

theorem summable_term_norm (c : L1 ι) :
    Summable (fun i => ‖c i • delta o (e i).val‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_bound o e B hb c)
    ((summable_abs c).mul_right B)

theorem summable_term (c : L1 ι) : Summable (fun i => c i • delta o (e i).val) :=
  (summable_term_norm o e B hb c).of_norm

def synthesisLinear : L1 ι →ₗ[ℝ] FreeSpace o where
  toFun c := ∑' i, c i • delta o (e i).val
  map_add' c d := by
    simp only [lp.coeFn_add, Pi.add_apply, add_smul]
    exact Summable.tsum_add (summable_term o e B hb c) (summable_term o e B hb d)
  map_smul' r c := by
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_assoc, RingHom.id_apply]
    exact (summable_term o e B hb c).tsum_const_smul r

theorem synthesis_bound (c : L1 ι) :
    ‖synthesisLinear o e B hb c‖ ≤ B * ‖c‖ := by
  change ‖∑' i, c i • delta o (e i).val‖ ≤ B * ‖c‖
  calc
    _ ≤ ∑' i, ‖c i • delta o (e i).val‖ :=
      norm_tsum_le_tsum_norm (summable_term_norm o e B hb c)
    _ ≤ ∑' i, |c i| * B := Summable.tsum_le_tsum (term_bound o e B hb c)
      (summable_term_norm o e B hb c) ((summable_abs c).mul_right B)
    _ = B * ‖c‖ := by rw [tsum_mul_right, norm_eq_tsum, mul_comm]

def synthesis : L1 ι →L[ℝ] FreeSpace o :=
  (synthesisLinear o e B hb).mkContinuous B (synthesis_bound o e B hb)

@[simp] theorem synthesis_apply (c : L1 ι) :
    synthesis o e B hb c = ∑' i, c i • delta o (e i).val := rfl

@[simp] theorem synthesis_single (i : ι) (r : ℝ) :
    synthesis o e B hb (lp.single 1 i r) = r • delta o (e i).val := by
  rw [synthesis_apply]
  simp only [lp.single_apply, Pi.single_apply, ite_smul, zero_smul]
  exact tsum_ite_eq i (fun j => r • delta o (e j).val)

omit hb in
@[simp] theorem analysis_delta (i : ι) :
    analysis o sep e (delta o (e i).val) = lp.single 1 i 1 := by
  apply lp.ext
  funext j
  have heq : (e i).val = (e j).val ↔ i = j := by
    constructor
    · intro h
      exact e.injective (Subtype.ext h)
    · rintro rfl
      rfl
  simp [analysis_apply, coordinate_delta, (e j).property, heq,
    lp.single_apply, Pi.single_apply, eq_comm]

@[simp] theorem analysis_synthesis (c : L1 ι) :
    analysis o sep e (synthesis o e B hb c) = c := by
  apply lp.ext
  funext i
  rw [analysis_apply, synthesis_apply,
    (coordinate o sep (e i).val).map_tsum (summable_term o e B hb c)]
  have heq (j : ι) : (e j).val = (e i).val ↔ j = i := by
    constructor
    · intro h
      exact e.injective (Subtype.ext h)
    · rintro rfl
      rfl
  simp [map_smul, coordinate_delta, (e i).property, heq, smul_eq_mul]

@[simp] theorem synthesis_analysis (u : FreeSpace o) :
    synthesis o e B hb (analysis o sep e u) = u := by
  let A := (synthesis o e B hb).comp (analysis o sep e)
  change A u = u
  refine freeSpace_induction (fun v => A v = v)
    (isClosed_eq A.continuous continuous_id) ?_ ?_ ?_ ?_ u
  · exact map_zero A
  · intro v w hv hw
    simp only [map_add, hv, hw]
  · intro r v hv
    simp only [map_smul, hv]
  · intro x
    by_cases hx : x = o
    · subst x
      simp [A]
    · obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      have hix : (e i).val = x := congrArg Subtype.val hi
      rw [← hix]
      change synthesis o e B hb (analysis o sep e (delta o (e i).val)) = _
      rw [analysis_delta, synthesis_single, one_smul]

def equiv : L1 ι ≃L[ℝ] FreeSpace o where
  toLinearEquiv :=
    { (synthesis o e B hb).toLinearMap with
      invFun := analysis o sep e
      left_inv := analysis_synthesis o sep e B hb
      right_inv := synthesis_analysis o sep e B hb }
  continuous_toFun := (synthesis o e B hb).continuous
  continuous_invFun := (analysis o sep e).continuous

@[simp] theorem equiv_apply (c : L1 ι) :
    equiv o sep e B hb c = ∑' i, c i • delta o (e i).val := rfl

end Coefficients

end DiscreteFree
end

end OAI


