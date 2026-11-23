-- Prove2me | Definitions.Def_GL2QFT_Circuits_DgateStages
-- name    : GL2QFT_Circuits_DgateStages
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:42:06.180944+00:00
-- url     : https://prove2.me/theorems/707130d9-358b-42f3-acf5-8d0abdafd82f
-- title:
--   Compute–phase–uncompute stages for the Gauss gate $D_\gamma$
-- statement:
--   For the implementation of $D_\gamma$ in Lemma 6.28, put $\delta=\gamma-2\alpha$ when $c=c_\alpha$, and $\delta=\infty$ (the zero sentinel) when $c=c_\infty$. The compute stage writes $\delta$ into a clean register and applies the sign $\chi_{\gamma-\alpha}(-1)$, with an additional minus sign exactly when $\delta=0$. The middle stage applies Theorem 6.10's normalized Gauss phase $\Gamma_q$ to $\delta$, and the uncompute stage erases $\delta$ with the inverse sign. The extra sign handles $g_q(1)=-1$. The work register code consists of the padded $(\gamma,c)$ register followed by the tagged $\delta$ register.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573, Lemma 6.28 (Implementation of D_gamma), p.54; Definition 6.16 eqs. (148)-(149), p.50; Theorem 6.10 eq. (122), p.43.

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_GL2QFT_Supplement_AGammaGates

noncomputable section
open Classical
namespace GL2QFT
namespace Circuits
open GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

/-- The coherent source register $|\gamma\rangle|c\rangle$ of Definition 6.16. -/
abbrev DgateSource (D : FieldData) := D.Lab × Option D.Lab

/-- The source together with the clean work register holding $\alpha^{-1}b=\gamma-2\alpha$. -/
abbrev DgateMid (D : FieldData) := DgateSource D × Option D.Lab

/-- Lemma 6.28: for $c=|c_\alpha\rangle$, the computed work label is
$\alpha^{-1}b=\alpha^{-2}\gamma$, written $\gamma-2\alpha$ in exponent notation. -/
def dgateWork (D : FieldData) (x : DgateSource D) : Option D.Lab :=
  match x.2 with
  | none => none
  | some α => some (x.1 - 2 * α)

/-- The sign applied while computing the work label. Here $b=\gamma-\alpha$; the extra minus
sign on $\gamma-2\alpha=0$ compensates the value $g_q(1)=-1$ of the Gauss phase on the trivial
character. -/
def dgateSign (D : FieldData) (x : DgateSource D) : ℂ :=
  match x.2 with
  | none => 1
  | some α =>
      let b := x.1 - α
      if x.1 - 2 * α = 0 then -D.chi b (-1) else D.chi b (-1)

/-- The normalized Gauss phase $\Gamma_q$ of Theorem 6.10, on the multiplicative tagged domain. -/
def gaussPhase (D : FieldData) : Matrix (Option D.Lab) (Option D.Lab) ℂ :=
  Matrix.diagonal fun c =>
    match c with
    | none => 1
    | some α => if α = 0 then -1 else D.gauss α * FieldData.isqrt D.q

/-- Reversible computation of the work label, including the sign $s(\gamma,c)$ above. -/
def dgateComputeMat (D : FieldData) : Matrix (DgateMid D) (DgateSource D) ℂ :=
  Matrix.of fun out inp => if out = (inp, dgateWork D inp) then dgateSign D inp else 0

/-- Clean uncomputation of the work label, with the inverse sign. -/
def dgateUncomputeMat (D : FieldData) : Matrix (DgateSource D) (DgateMid D) ℂ :=
  Matrix.of fun out inp => if inp = (out, dgateWork D out) then (dgateSign D out)⁻¹ else 0

/-- The padded coherent source register followed by the tagged work register. -/
def dgateMidCode (D : FieldData) (x : DgateMid D) :
    Qubits (((D.r + 1) * D.labW + (D.r + 1) * D.labW) + (D.r + 1) * D.labW) :=
  appendCode (fun y : DgateSource D => padTo ((D.r + 1) * D.labW + (D.r + 1) * D.labW)
    (D.gammaInCode y)) (fun c : Option D.Lab => D.tagCode (D.xEmb c)) x

end Circuits
end GL2QFT


