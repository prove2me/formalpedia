-- Prove2me | Definitions.Def_Transport_PhysicalLow_NormalizedProbe
-- name    : Transport_PhysicalLow_NormalizedProbe
-- status  : Definition
-- author  : @Himan
-- created : 2026-11-15T03:24:38.213517+00:00
-- url     : https://prove2.me/theorems/233de9a9-f62f-47fe-a2d6-fe9d33dca37d
-- title:
--   The tuned normalized physical probe with Gram scales $Z^{\ell_x}$, $Z^{\ell_y}$
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$, a *Hecke character* is a finite-order Hecke character of $\mathbb Q(\zeta_3)$ in OpenAI's family-003 development, and $\beta$ is the supremum of the real parts of the zeros of the associated Hecke $L$-functions (pole exception excluded, sentinel at $1/2$). The tuned constants of LW56e2's refinement are $p=214651/1250000000$, the Gram exponent $b=192821/1562500$, the total slot length $\ell=\tfrac16+p$, the row and column exponents $\ell_x=(1-\ell-b)/2$ and $\ell_y=(1-\ell+b)/2$, the conductor exponent $h=(1+3\ell+b)/2$, the cushion $\zeta=1/(8\cdot 10^{12})$, the boundary $B=\tfrac{11}{12}-\tfrac{\ell}{4}=4374785349/5000000000$ and the signal exponent $\operatorname{sig}(s)=s+\ell_x/2-1+h/6=s-2147607/3125000$.
--
--   This file defines the probe function of the tuned argument. It is OpenAI's normalized physical probe with the three numerical exponents of the original construction replaced by the tuned ones.
--
--   Let $M\subset\mathcal O$ be a nonzero ideal, $H$ a subgroup of $(\mathcal O/M)^\times$, $S$ a finite set of maximal ideals with nonzero product, $\ell_1,\dots,\ell_K$ real slot lengths, $0<a\le b$ a support window, $W_1,\dots,W_K:\mathbb R\to\mathbb R$ slot profiles, $W^0,W^1$ Schwartz functions and $\eta$ a Hecke character. For $Z>0$ put $Y_j=Z^{\ell_j}$, and let $T_j$ be the pool of prime ideals outside $S$ in the identity ray class modulo $(M,H)$ with norm in the window $[aY_j,bY_j]$. The tuned normalized probe is
--   $$
--   J(Z)=\frac{\mathcal P_\eta\big(Z^{\ell_x},\,Z^{\ell_y},\,Z\big)}{c(W^0,W^1,S)\cdot \Pi\big(Z,\ell,(m_j)_j\big)},
--   $$
--   where $\mathcal P_\eta(X,Y,Z)$ is the source's compensated physical probe of $\eta$ built from the calibration data of $S$, the canonical slot supports of the pools $T_j$, the slot profiles $W_j$ at scales $Y_j$, and the Gram scales $X,Y$; $c(W^0,W^1,S)$ is the source residue constant for the modulus $\prod_{P\in S}P$; and $\Pi(Z,\ell,m)$ is the principal scalar over all $K$ slots with total length $\ell$ and slot masses $m_j$ computed from the pools and the residue weights of the $W_j$.
--
--   OpenAI's original `normalizedProbe` is the same expression with $(\ell_x,\ell_y,\ell)=(17/48,\,23/48,\,1/6)$. The low-side and the high-side estimates of the refinement are both statements about this one function, which is why it is isolated as a definition.
--
--   **Formalization Note** Transcribed verbatim from the source. `compensatedPhysicalProbe`, `calibrationForSet`, `canonicalSlotSupport`, `pool`, `sourceResidueConstant`, `Probe.principalScalar`, `slotMass` and `residueWeights` are the platform's port of OpenAI's objects (bundles up to `OAIHecke78B022`). The value at $Z$ is a quotient in $\mathbb C$, with Lean's convention $x/0=0$.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalLow/NormalizedProbe.lean, def tunedNormalizedProbe (L18-L28), adapted from OpenAI math, Detector/FinalAssemblySource.lean (normalizedProbe): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalLow/NormalizedProbe.lean#L18-L28

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022
import Definitions.Def_Transport_TunedCandidate

set_option autoImplicit false

/-! The actual tuned normalized probe.
Adapted from OpenAI Detector/FinalAssemblySource.lean, pinned source commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
This definition is shared verbatim by the low, high and principal proofs. -/

namespace RH.Transport.PhysicalLow

noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

def tunedNormalizedProbe {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (ell : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ) : ℂ :=
  let Yp := fun j=>Z^(ell j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j=>canonicalSlotSupport (T j)) (fun j y=>(W j y:ℂ)) Yp
    (Z^TunedCandidate.lx) (Z^TunedCandidate.ly) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z TunedCandidate.ell (slotMass T (residueWeights W Yp)) : ℂ))

end
end RH.Transport.PhysicalLow


