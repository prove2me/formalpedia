-- Prove2me | Definitions.Def_MonotoneCompStatics_QSMChar_Supplement_Utility
-- name    : MonotoneCompStatics_QSMChar_Supplement_Utility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:05:47.284848+00:00
-- url     : https://prove2.me/theorems/2573cdfe-5941-4834-8c40-aa65e77802fa
-- title:
--   Completely regular utilities, marginal ratios and lexicographic comparisons
-- statement:
--   Let $U:\mathbb R^3\to\mathbb R$ be a utility function. Complete regularity means that $U$ is continuously differentiable and every nonempty fixed-type level set $\{(x,y):U(x,y,t)=c\}$ is path connected. Empty levels are allowed. Define
--   $$R_U(x,y,t)=\frac{\partial_xU(x,y,t)}{|\partial_yU(x,y,t)|}.$$
--   The weak and strict Spence–Mirrlees conditions say that this ratio is, respectively, nondecreasing and strictly increasing in $t$ for every fixed $(x,y)$. Theorems using the ratio explicitly require $U_y\ne0$ everywhere. Lexicographic single crossing applies the published comparison predicates to choices $(x,y)$ ordered by $x$ first, then by $y$ on ties. The utility $U_0(x,y,t)=tx^3+y$ is also named for the source-error witnesses.
--
--   These predicates separate analytic regularity, ordinal comparisons and differential conditions. **Formalization Note** Differentiability is joint on $\mathbb R^3$, represented by nested real products. Path connectedness is required only for nonempty levels. No condition $U_x\ne0$ is imposed.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), DOI 10.2307/2951479, pp.160–161, PDF 5–6; Theorems 3 and 11 (counterexample construction)

import Mathlib
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing
import Definitions.Def_MonotoneCompStatics_Monotonicity_StrictSingleCrossing

namespace MonotoneCompStatics.QSMChar.Supplement

/-- Completely regular utility: C¹ and path-connected fixed-type indifference sets.
Empty level sets are permitted, as with the usual connectedness convention. -/
def CompletelyRegular (U : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ => U p.1.1 p.1.2 p.2) ∧
    ∀ t c : ℝ, {p : ℝ × ℝ | U p.1 p.2 t = c} = ∅ ∨
      IsPathConnected {p : ℝ × ℝ | U p.1 p.2 t = c}

noncomputable def marginalRatio (U : ℝ → ℝ → ℝ → ℝ) (x y t : ℝ) : ℝ :=
  deriv (fun a => U a y t) x / |deriv (fun b => U x b t) y|

def SpenceMirrlees (U : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, Monotone (marginalRatio U x y)

def StrictSpenceMirrlees (U : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, StrictMono (marginalRatio U x y)

def LexSingleCrossing (U : ℝ → ℝ → ℝ → ℝ) : Prop :=
  MonotoneCompStatics.Monotonicity.SingleCrossing
    (fun p : Lex (ℝ × ℝ) => U (ofLex p).1 (ofLex p).2)

def LexStrictSingleCrossing (U : ℝ → ℝ → ℝ → ℝ) : Prop :=
  MonotoneCompStatics.Monotonicity.StrictSingleCrossing
    (fun p : Lex (ℝ × ℝ) => U (ofLex p).1 (ofLex p).2)

/-- Smooth counterexample to the printed strict converses of Theorems 3 and 11. -/
def cubicUtility (x y t : ℝ) : ℝ := t * x ^ 3 + y

end MonotoneCompStatics.QSMChar.Supplement


