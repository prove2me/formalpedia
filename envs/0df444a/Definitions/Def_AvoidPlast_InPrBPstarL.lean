-- Prove2me | Definitions.Def_AvoidPlast_InPrBPstarL
-- name    : AvoidPlast_InPrBPstarL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:39.451896+00:00
-- url     : https://prove2.me/theorems/f96d5cb5-51af-4a5f-b45e-bf91e6264dd9
-- title:
--   The class prBP$^*$L
-- statement:
--   A promise problem $\Pi$ is in **prBP$^*$L** if there are a machine $M$ with read-only tapes $x$ and $\rho$ and a constant $C$ such that, with $R(n)=C(n^C+1)$: on every $x$ and $\rho\in\{0,1\}^{R(|x|)}$, $M$ halts within $R(|x|)$ steps with work space at most $C(\log_2(|x|+2)+1)$; $\Pr_\rho[M(x,\rho)\text{ accepts}]\ge 2/3$ on yes-instances and $\le 1/3$ on no-instances. This is the class of Nisan: logspace and polynomial time, with persistent two-way read-only randomness that does not count towards the space.
--
--   **Formalization Note** The length of $\rho$ is the machine's own time bound. A free length function would act as non-uniform advice (the machine can measure $|\rho|$), would put undecidable unary languages in the class and would make $\mathrm{prBP}^*\mathrm{L}=\mathrm{prL}$ false outright. The head on $\rho$ may also jump, which within polynomial time and logspace is simulated by a walk.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 1.2, p.3

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_workSpace
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_lg

namespace AvoidPlast

/-- The class prBP\*L (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §1.2, p.3): promise problems solvable by probabilistic machines
"running in logspace and polynomial time whose randomness is stored on a special tape to which they
have persistent two-way read-only access (and the contents of this tape does not count towards the
machine's space complexity)".

**Formalization Note** The random string `ρ` has the fixed polynomial length `C · (n^C + 1)`, the
machine's own time bound, so that its length carries no non-uniform advice (a free length function
would put undecidable unary languages in the class and make `prBP*L = prL` false outright). The
read-only head on `ρ` moves two-way and may also jump (reading R5); within polynomial time and
logspace a jump can be replaced by a walk. -/
def InPrBPstarL (P : KarpLiptonOM.PromiseProblem) : Prop :=
  ∃ (M : Machine 2) (C : ℕ),
    (∀ x ρ : List Bool, ρ.length = C * (x.length ^ C + 1) →
      HaltsWithin M ![x, ρ] (C * (x.length ^ C + 1)) ∧
      (workSpace M ![x, ρ] : ℝ) ≤ C * (lg x.length + 1)) ∧
    (∀ x ∈ P.yes, (2 : ℝ) / 3 ≤ prob (C * (x.length ^ C + 1)) fun ρ => Accepts M ![x, ρ]) ∧
    (∀ x ∈ P.no, prob (C * (x.length ^ C + 1)) (fun ρ => Accepts M ![x, ρ]) ≤ (1 : ℝ) / 3)

end AvoidPlast


