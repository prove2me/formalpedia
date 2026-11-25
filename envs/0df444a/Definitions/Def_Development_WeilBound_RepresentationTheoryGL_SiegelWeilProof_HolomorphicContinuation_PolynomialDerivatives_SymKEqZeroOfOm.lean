-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T12:15:38.3984+00:00
-- url     : https://prove2.me/theorems/61d48ae3-80d9-5b87-98fe-4b9be5b969b7
-- title:
--   Sym KEq Zero Of Om
-- statement:
--   Definitions and structural lemmas for Sym KEq Zero Of Om, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/SymKEqZeroOfOm.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymbolFirstFamilyOfMem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreD_symK_mem

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
namespace CoreD
variable {m n : ℕ} {ε : Fin m → Bool}
def psi (p q : Sym m n) : ℂ :=
  ∑ u ∈ p.support ∪ q.support, star (p.coeff u) * q.coeff u * ∏ k ∈ u.support, ((u k).factorial : ℂ)
variable (ε) in

def Om : Module.End ℂ (Sym m n) :=
  ∑ ij : Fin n × Fin n, (symK ε ij.1 ij.2).toLinearMap * (symK ε ij.2 ij.1).toLinearMap
theorem Om_apply (s : Sym m n) : Om ε s = ∑ ij : Fin n × Fin n, symK ε ij.1 ij.2 (symK ε ij.2 ij.1 s) := by
  simp [Om, LinearMap.sum_apply]
theorem Om_mem {N : ℕ} {s : Sym m n} (hs : s ∈ S ε N) : Om ε s ∈ S ε N := by
  rw [Om_apply]
  exact Submodule.sum_mem _ fun ij _ => symK_mem _ _ (symK_mem _ _ hs)
variable (ε) in

def OmS (N : ℕ) : Module.End ℂ (S (n := n) ε N) := (Om ε).restrict fun _ hs => Om_mem hs
section adj
variable (hadj : ∀ (i j : Fin n) (s t : Sym m n), psi (symK ε i j s) t = psi s (symK ε j i t))
include hadj
end adj
end CoreD
end PositivityTheory.Rg.Sw.LC


