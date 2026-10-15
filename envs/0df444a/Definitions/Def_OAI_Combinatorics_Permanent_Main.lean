-- Prove2me | Definitions.Def_OAI_Combinatorics_Permanent_Main
-- name    : OAI_Combinatorics_Permanent_Main
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T17:49:57.052933+00:00
-- url     : https://prove2.me/theorems/ab48ba9d-4687-4755-8f83-c2c9488cac82
-- title:
--   Explicit exponent $p_0=2-10^{-5}$ and radius $\varepsilon_0=10^{-5}$ for the robust four-row permanent inequality
-- statement:
--   This module fixes the two explicit absolute constants for which the robust four-row permanent inequality is established.
--
--   1. **Strict exponent.** $p_0=2-\dfrac{1}{100000}=2-10^{-5}$.
--
--   2. **Robust radius.** $\varepsilon_0=\dfrac{1}{100000}=10^{-5}$.
--
--   They satisfy $9/5\le p_0<2$ (in particular $4/3<p_0<2$) and $\varepsilon_0>0$. With these values one has the following: for every probability law $\nu$ on the symmetric group $S_4$ with uniform marginals ($\sum_{\pi:\,\pi(i)=j}\nu(\pi)=\tfrac14$ for all sites $i,j$) whose total variation distance $\tfrac12\sum_{\pi}\bigl|\nu(\pi)-\tfrac1{24}\bigr|$ from the uniform law is less than $\varepsilon_0$, and for every real $4\times4$ array $f$ with nonnegative entries,
--   $$
--   \sum_{\pi\in S_4}\nu(\pi)\prod_{i=0}^{3}f_{i\pi(i)}\le\prod_{i=0}^{3}\Bigl(\frac14\sum_{j=0}^{3}f_{ij}^{\,p_0}\Bigr)^{1/p_0}.
--   $$
--   The constants serve as the explicit witnesses $p_0$ and $\varepsilon$ in the existential form of this inequality. They are chosen so that, for rows normalized by $\sum_jf_{ij}^2=4$ and with $\Delta(f)=\sum_{i,j}(f_{ij}-1)^2$, the gain $\Delta(f)/1728$ of the exponent-two stability estimate for the uniform law dominates the sum of the loss $6\,\varepsilon_0\,\Delta(f)$ caused by perturbing the law and the loss $\tfrac58(2-p_0)\,\Delta(f)$ caused by lowering the exponent.
--
--   **Formalization Note** The constants are the real numbers `strictExponent`, defined as `2 - 1 / 100000`, and `robustRadius`, defined as `1 / 100000`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Permanent/Main.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Permanent/Main.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FourRowPermanent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FourRowPermanent
import Definitions.Def_OAI_Combinatorics_Permanent_Stability

namespace OAI

noncomputable section
namespace FourRow
open scoped BigOperators

def strictExponent : ℝ := 2 - 1 / 100000

def robustRadius : ℝ := 1 / 100000

/- Homogeneity extends the bound to unrestricted nonnegative rows. -/
end FourRow
end

end OAI


