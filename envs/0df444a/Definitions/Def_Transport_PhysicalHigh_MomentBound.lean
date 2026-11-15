-- Prove2me | Definitions.Def_Transport_PhysicalHigh_MomentBound
-- name    : Transport_PhysicalHigh_MomentBound
-- status  : Definition
-- author  : @Himan
-- created : 2026-11-15T03:26:28.283418+00:00
-- url     : https://prove2.me/theorems/365def60-c3f2-4c06-99df-d158b581f8df
-- title:
--   The tuned source moment bound for all row subsets of the central partition
-- statement:
--   Throughout, $\mathcal O=\mathbb Z[\zeta_3]$, a *Hecke character* is a finite-order Hecke character of $\mathbb Q(\zeta_3)$ in OpenAI's family-003 development, and $\beta$ is the supremum of the real parts of the zeros of the associated Hecke $L$-functions (pole exception excluded, sentinel at $1/2$). The tuned constants of LW56e2's refinement are $p=214651/1250000000$, the Gram exponent $b=192821/1562500$, the total slot length $\ell=\tfrac16+p$, the row and column exponents $\ell_x=(1-\ell-b)/2$ and $\ell_y=(1-\ell+b)/2$, the conductor exponent $h=(1+3\ell+b)/2$, the cushion $\zeta=1/(8\cdot 10^{12})$, the boundary $B=\tfrac{11}{12}-\tfrac{\ell}{4}=4374785349/5000000000$ and the signal exponent $\operatorname{sig}(s)=s+\ell_x/2-1+h/6=s-2147607/3125000$.
--
--   This file defines the moment hypothesis that links the two halves of the high-side estimate at the tuned boundary: one theorem produces it, the other consumes it.
--
--   Let $F$ be source data, $D$ tuned data with slot lengths $(\ell_j)$ and detector scale $\varepsilon=D.P.\varepsilon$, and let `counts` be count parameters for the modulus of $F$ at the reserved loss $t=10^{-15}$, with constants $(c_B,k_B)$ for the balanced range and $(c_H,k_H)$ for the high range. For a Hecke character $\eta$ and reals $Z,\tau,C,\mathrm{height}$, the proposition $\mathrm{TSMB}(F,D,\mathrm{counts};\eta,Z,\tau,C,\mathrm{height})$ asserts:
--
--   for every finite set of free rows all of norm at least $Z^{1/100}$, every conductor exponent $d\ge 1/200$, all reals $a,d_{\max}$, slot mesh and bin width, every $i\in\mathbb N$ and every complex $z$ with $\operatorname{Re}z=17/50$ and $|\operatorname{Im}z|\le\mathrm{height}$, OpenAI's source moment statement `SourceMomentsAt` holds for the detector batches of $\eta$ on those rows, with slot widths $\ell_j/d$, profile the window of $F$, upper bound $2$, external point $z$, moment loss $0$, moment constant $C$, the given height and error $t$, and with the count constants
--   $$
--   (c,k)=\begin{cases}(c_B,k_B)&\text{if }2a-1\le 5/6,\\ (c_H,k_H)&\text{otherwise.}\end{cases}
--   $$
--
--   **Formalization Note** Transcribed verbatim from the source. `SourceMomentsAt`, `CountParameters`, `FreeRow` and `rowNorm` are the platform's port of OpenAI's objects (bundle `OAIHecke78B027`); the precise content of a moment statement for a detector batch is the one fixed there.
-- source:
--   LW56e2, quasi-riemann-improved, commit b83dbbd914c5751acf9bc3389cde58970437278f, lean/Transport/PhysicalHigh/MomentBound.lean, def TunedSourceMomentBound (L13-L23): https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/PhysicalHigh/MomentBound.lean#L13-L23

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Definitions.Def_Transport_PhysicalHigh_TunedData

set_option autoImplicit false

namespace RH.Transport.PhysicalHigh
noncomputable section
open scoped Classical
open Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbeFinalAssembly ProbeHighRowFamily HeckeInverseAmplification

/-- Actual moment fields for all row subsets needed by the central partition. -/
def TunedSourceMomentBound {Δ : ℝ} {seed : Parameters.HighData Δ} (F : SourceData seed)
    {Kmin : ℕ} {allowance : ℝ} (D : TunedData Kmin allowance)
    (counts : CountParameters F.modulus ⊤ reservedLoss)
    (η : Character) (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
  ∀d : ℝ,(1/200:ℝ)≤d→∀a dmax slotMesh binWidth : ℝ,∀i : ℕ,∀z : ℂ,
  z.re=17/50→|z.im|≤height→
  SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
    (fun _ y=>(F.w y:ℂ)) Z d a D.P.ε τ dmax 2 slotMesh binWidth i z 0
    (if 2*a-1≤5/6 then counts.cB else counts.cH)
    (if 2*a-1≤5/6 then counts.kB else counts.kH) C height reservedLoss

end
end RH.Transport.PhysicalHigh


