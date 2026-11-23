-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FockMono
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FockMono
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:44.796057+00:00
-- url     : https://prove2.me/theorems/a601802b-7e8e-475a-a7d6-e8d86a321ccf
-- title:
--   Fock Mono
-- statement:
--   Definitions and structural lemmas for Fock Mono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/FockMono.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
def cr (c : ℝ) (k : Fin m × Fin n × Bool) : Module.End ℂ (PX m n) :=
  if k.2.2 then -((pderiv (R := ℂ) k).toLinearMap : Module.End ℂ (PX m n)) + (2 * c : ℂ) • LinearMap.mulLeft ℂ (X (k.1, k.2.1, false) : PX m n)
  else -((pderiv (R := ℂ) k).toLinearMap : Module.End ℂ (PX m n)) + (2 * c : ℂ) • LinearMap.mulLeft ℂ (X (k.1, k.2.1, true) : PX m n)
def fockMono (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : PX m n :=
  (((Finset.univ : Finset (Fin m × Fin n × Bool)).toList.map fun k => (cr c k) ^ (s k)).prod) 1
def fock (c : ℝ) (p : PX m n) : PX m n := ∑ s ∈ p.support, p.coeff s • fockMono c s
def Dop (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (p : PX m n) : PX m n :=
  if ε a = ε b then
    ∑ i, (X (b, i, true) * pderiv (a, i, true) p - X (a, i, false) * pderiv (b, i, false) p)
  else
    ∑ i, ((2 * c : ℂ) • pderiv (b, i, false) (pderiv (a, i, true) p) - (1 / (2 * c) : ℂ) • (X (a, i, false) * X (b, i, true) * p))
def contr (c : ℝ) (p : PX m n) : ℂ :=
  ∑ s ∈ p.support, if ∀ a i, s (a, i, false) = s (a, i, true) then
    p.coeff s * ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0
def KopL (ε : Fin m → Bool) (i j : Fin n) : Module.End ℂ (PX m n) :=
  ∑ a ∈ Finset.univ.filter (fun a => ε a = true), LinearMap.mulLeft ℂ (X (a, i, false) : PX m n) ∘ₗ (pderiv (R := ℂ) (a, j, false)).toLinearMap -
    ∑ a ∈ Finset.univ.filter (fun a => ε a = false), LinearMap.mulLeft ℂ (X (a, j, true) : PX m n) ∘ₗ (pderiv (R := ℂ) (a, i, true)).toLinearMap
def mulQ (ε : Fin m → Bool) (i j : Fin n) (P : PX m n) : PX m n := Qp ε i j * P
def lapS (ε : Fin m → Bool) (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, C (sgn ε a) * (pderiv (a, i, false) (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P) -
    C (c : ℂ) * X (a, i, true) * (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P))
def eulH (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, X (a, j, false) * (pderiv (a, i, false) P - C (c : ℂ) * X (a, i, true) * P)
def eulA (c : ℝ) (i j : Fin n) (P : PX m n) : PX m n :=
  ∑ a, X (a, i, true) * (pderiv (a, j, true) P - C (c : ℂ) * X (a, j, false) * P)
def kAlg (ε : Fin m → Bool) : Subalgebra ℂ (Module.End ℂ (PX m n)) :=
  Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => KopL ε ij.1 ij.2)
end PositivityTheory.Rg.Sw.LC


