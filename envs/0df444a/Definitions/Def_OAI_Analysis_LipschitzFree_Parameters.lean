-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
-- name    : OAI_Analysis_LipschitzFree_Parameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:58:05.803882+00:00
-- url     : https://prove2.me/theorems/d0c3fca4-e3af-4782-b900-827239eace84
-- title:
--   Numerical parameters of the metric blocks for a norm bound $p$
-- statement:
--   For a natural number $p$ (the bound on operator norms in the block statement) this file fixes the following natural numbers, each defined in terms of the previous ones:
--   $$L=10p,\qquad R=3L,\qquad K=10p\,(R+1),\qquad D=K+2L+5,\qquad B=4R+D,\qquad V=1+4pB,$$
--   $$g=20V+2,\qquad \Delta=2g,\qquad Q=\Delta^{2L+1},\qquad H=\Delta^{D+1},\qquad c=2\,\Delta\,Q\,H+1 .$$
--   All of them are functions of $p$. Explicitly $R=30p$, $K=300p^2+10p$, $D=300p^2+30p+5$ and $B=300p^2+150p+5$, which is the diameter bound $300p^2+150p+5$ appearing in the block statement. The file also records the positivity facts $L>0$ and $R>0$ for $p\ge1$, and $c>0$ for every $p$.
--
--   In the construction of the metric block for the bound $p$, $L$ and $K$ are the height and the width of the Lipschitz bump tests, $R$ is the length of the edges that attach vertices to their label anchors, $D$ is the cap of the distance labels, $B$ bounds the diameter of the block, and $V$ bounds the total variation of the coefficient vectors produced by an operator. Further, $g$ is the number of free generators and $\Delta=2g$ the number of ports (one for each generator and one for its inverse); $Q$ and $H$ are the bounds $\Delta^{n+1}$ for the number of words of length at most $n=2L$ and $n=D$ over $\Delta$ ports; and $c$ is the number of colours.
--
--   **Formalization Note** The parameters are the natural-number functions `L`, `R`, `K`, `D`, `B`, `V`, `generators` ($g$), `degree` ($\Delta$), `Q`, `H`, `colors` ($c$), defined for every $p\in\mathbb{N}$ (including $p=0$). The positivity lemmas are `L_pos`, `R_pos` (both assuming $1\le p$) and `colors_pos`. The closed forms above are consequences of the definitions and are not stated in this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/Parameters.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Parameters.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model

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

theorem L_pos {p : ℕ} (hp : 1 ≤ p) : 0 < L p := by dsimp [L]; omega

theorem R_pos {p : ℕ} (hp : 1 ≤ p) : 0 < R p := by dsimp [R]; exact Nat.mul_pos (by omega) (L_pos hp)

theorem colors_pos (p : ℕ) : 0 < colors p := by dsimp [colors]; omega

end DiscreteFree.BlockParameters

end

end OAI


