-- Prove2me | Definitions.Def_Transport_DataProbe
-- name    : Transport_DataProbe
-- status  : Definition
-- author  : @Himan
-- created : 2026-11-15T03:25:35.396449+00:00
-- url     : https://prove2.me/theorems/b18ab357-6556-4c83-b9d4-4188a04ad416
-- title:
--   The data probe $J_{F,D,\eta}$ attached to source data $F$ and tuned data $D$
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$, a *Hecke character* is a finite-order Hecke character of $\mathbb Q(\zeta_3)$ in OpenAI's family-003 development, and $\beta$ is the supremum of the real parts of the zeros of the associated Hecke $L$-functions (pole exception excluded, sentinel at $1/2$). The tuned constants of LW56e2's refinement are $p=214651/1250000000$, the Gram exponent $b=192821/1562500$, the total slot length $\ell=\tfrac16+p$, the row and column exponents $\ell_x=(1-\ell-b)/2$ and $\ell_y=(1-\ell+b)/2$, the conductor exponent $h=(1+3\ell+b)/2$, the cushion $\zeta=1/(8\cdot 10^{12})$, the boundary $B=\tfrac{11}{12}-\tfrac{\ell}{4}=4374785349/5000000000$ and the signal exponent $\operatorname{sig}(s)=s+\ell_x/2-1+h/6=s-2147607/3125000$.
--
--   This file defines the single probe function that enters both estimates of the uniform common probe contract at the tuned boundary.
--
--   Let $F$ be OpenAI's source data over some high-side seed: a finite set $F.S$ of prime (maximal) ideals of $\mathcal O$ satisfying the source exclusions, with modulus $\prod_{P\in F.S}P$, together with a fixed smooth window $w$ supported in $(1,2)$ and its Schwartz version $W$. Let $D$ be tuned data in the sense of `Transport_PhysicalHigh_TunedData`, with $K$ slots of lengths $\ell_1,\dots,\ell_K$. For a Hecke character $\eta$ the data probe is the tuned normalized probe
--   $$
--   J_{F,D,\eta}(Z)=J\big(M=\textstyle\prod_{P\in F.S}P,\ H=\top,\ S=F.S,\ (\ell_j)_j,\ a=1,\ b=2,\ W_j=w,\ W^0=W^1=W,\ \eta\big)(Z),
--   $$
--   a function $\mathbb R\to\mathbb C$. Only the slot lengths of $D$ enter; the same window is used in every slot.
--
--   The low-side bound $J_{F,D,\eta}(Z)=O(Z^{\operatorname{sig}(B)+\omega})$ and the high-side comparison of $J_{F,D,\eta}$ with the Hecke signal are proved separately in the source and combined in `actual_uniform_common_probe`; sharing one literal function is what makes the two estimates combinable.
--
--   **Formalization Note** Transcribed verbatim from the source. `SourceData` and its fields come from the platform bundle `OAIHecke78B024`; `tunedNormalizedProbe` from `Transport_PhysicalLow_NormalizedProbe`. The instance that the modulus is nonzero is supplied inside the definition from `fixedPrimeProduct_ne_zero`, exactly as in the source.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/DataProbe.lean, def dataProbe (L13-L18): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/DataProbe.lean#L13-L18

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024
import Definitions.Def_Transport_PhysicalLow_NormalizedProbe
import Definitions.Def_Transport_PhysicalHigh_TunedData

set_option autoImplicit false

namespace RH.Transport
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeFinalAssembly

/-- One literal normalized physical probe, shared by the low and high proofs. -/
def dataProbe {Δ : ℝ} {seed : Parameters.HighData Δ} (F : SourceData seed)
    {Kmin : ℕ} {allowance : ℝ} (D : PhysicalHigh.TunedData Kmin allowance)
    (η : Character) : ℝ→ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  PhysicalLow.tunedNormalizedProbe F.modulus ⊤ F.S F.maximal D.ell 1 2
    (fun _=>F.w) F.W F.W η

end
end RH.Transport


