-- Prove2me | Definitions.Def_NarrowDNF_BourgainParameters
-- name    : NarrowDNF_BourgainParameters
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:00.251198+00:00
-- url     : https://prove2.me/theorems/e725c475-d017-43e8-ae12-1a5cac2516af
-- title:
--   Explicit thresholds and support cutoffs in the Bourgain component estimate
-- statement:
--   For a natural degree cutoff $k$ and a real error parameter $\varepsilon$, define
--   $$\eta(k,\varepsilon)=\frac{\varepsilon^{10k}}{3^{10k^2}},\qquad
--   \tau(k,\varepsilon)=\frac{\varepsilon^3}{3^{6k}},\qquad
--   R(k,\varepsilon)=\frac{3^{18k}}{\varepsilon^{10}}.$$
--   The integer cutoff is the natural-number ceiling $r(k,\varepsilon)=\lceil R(k,\varepsilon)\rceil_+$.
--
--   In their analytic use, $\varepsilon>0$ and the stated upper bounds on the error parameter are supplied by the surrounding theorem. The symbol $\varepsilon$ is an error budget, not the base of the exponential function. The Fourier threshold $\eta$ retains the constants used in the paper; $\tau$ controls which coordinate square functions are considered large; and the ceiling cutoff turns the real support-size budget into an integer. The bundle fixes these numerical choices without asserting the component estimate that later connects them.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainParameters.lean#L16-L16
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainParameters.lean#L17-L17
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainParameters.lean#L18-L18
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainParameters.lean#L19-L19

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace NarrowDNF.BourgainParameters
end NarrowDNF.BourgainParameters


/-! Explicit numerical choices for the reconstructed Bourgain small-component
estimate. The Fourier threshold eta retains the paper's constants. -/

noncomputable section
namespace NarrowDNF.BourgainParameters

def eta (k : ℕ) (e : ℝ) : ℝ := e^(10*k) / (3:ℝ)^(10*k^2)
def tau (k : ℕ) (e : ℝ) : ℝ := e^3 / (3:ℝ)^(6*k)
def realCutoff (k : ℕ) (e : ℝ) : ℝ := (3:ℝ)^(18*k) / e^10
def cutoff (k : ℕ) (e : ℝ) : ℕ := ⌈realCutoff k e⌉₊























end NarrowDNF.BourgainParameters


