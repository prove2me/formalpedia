-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
-- name    : OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T11:54:56.626402+00:00
-- url     : https://prove2.me/theorems/6eb72196-22b0-4a64-899e-4395376758cc
-- title:
--   Explicit integer parameters of the metric-block construction, including $B(p)=300p^2+150p+5$
-- statement:
--   This file fixes the explicit natural-number parameters of the quantitative construction, all of them functions of a natural number $p$:
--   $$L(p)=10p,\qquad R(p)=3L(p),\qquad K(p)=10p\,\bigl(R(p)+1\bigr),\qquad D(p)=K(p)+2L(p)+5,$$
--   $$B(p)=4R(p)+D(p),\qquad V(p)=1+4p\,B(p),$$
--   together with the graph parameters
--   $$g(p)=20V(p)+2,\quad \Delta(p)=2g(p),\quad Q(p)=\Delta(p)^{2L(p)+1},\quad H(p)=\Delta(p)^{D(p)+1},\quad \kappa(p)=2\,\Delta(p)\,Q(p)\,H(p)+1 .$$
--
--   In closed form $R(p)=30p$, $K(p)=300p^2+10p$, $D(p)=300p^2+30p+5$, $B(p)=300p^2+150p+5$ and $V(p)=1200p^3+600p^2+20p+1$. The file also records that $\kappa(p)>0$ for every $p$.
--
--   These numbers calibrate the construction for a given $p$: the metric blocks use $R(p)$ as attachment scale and $D(p)$ as label cap, the underlying port graph has $g(p)$ generators and $\Delta(p)$ ports, and its vertices are coloured with $\kappa(p)$ colours. The quantity $B(p)=4R(p)+D(p)$ bounds the distances inside a block, and $B(p)=300p^2+150p+5$ is the constant appearing in the upper equivalence bound of the resulting renorming of $\ell^1$.
--
--   **Formalization Note** The parameters are the definitions `L`, `R`, `K`, `D`, `B`, `V`, `generators`, `degree`, `Q`, `H`, `colors` in the namespace `BlockParameters`, all maps from natural numbers to natural numbers, with the lemma `colors_pos`. No hypothesis on $p$ is imposed in this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Parameters.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Parameters.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RealL1Renorming mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs__RealL1Renorming

namespace OAI

/-!
# Quantitative block parameters and strict variation bounds
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.BlockParameters

def L (p : ℕ) := 10*p
def R (p : ℕ) := 3*L p
def K (p : ℕ) := 10*p*(R p+1)
def D (p : ℕ) := K p+2*L p+5
def B (p : ℕ) := 4*R p+D p
def V (p : ℕ) := 1+4*p*B p

def generators (p : ℕ) := 20*V p+2
def degree (p : ℕ) := 2*generators p
def Q (p : ℕ) := degree p^(2*L p+1)
def H (p : ℕ) := degree p^(D p+1)
def colors (p : ℕ) := 2*degree p*Q p*H p+1

theorem colors_pos (p : ℕ) : 0 < colors p := by dsimp [colors]; omega

end DiscreteFree.BlockParameters

end

end OAI


