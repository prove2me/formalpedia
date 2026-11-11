-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_predPhaseState
-- name    : UnitaryQIPPSPACE_predPhaseState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:39.253412+00:00
-- url     : https://prove2.me/theorems/85e828f7-badf-4bab-a66f-dccd9fc74728
-- title:
--   The phase state $|\varphi_{\Gamma_{z,m}}\rangle$ of a predicate
-- statement:
--   A predicate $\Gamma(z,x)$ on pairs of strings is a language read on the pair code $\mathrm{tup}[z,x]$. For $z$ and $m$, $\Gamma_{z,m}(x)=\Gamma(z,x)$ for $x\in\{0,1\}^m$, and $|\varphi_{\Gamma_{z,m}}\rangle$ is its Boolean phase state.
--
--   These are the target states of the state-synthesis subprotocols (Lemma 4.16).
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Lemma 4.16, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_UnitaryQIPPSPACE_boolPhaseGate

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

open Classical in
/-- **The phase state `|φ_{Γ_{z,m}}⟩` of a predicate** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, Lemma 4.16, p. 31 (PDF p. 33)): "where
`Γ_{z,m} : {0,1}^m → {0,1}` is defined by `Γ_{z,m}(x) = Γ(z, x)`, and `|φ_{Γ_{z,m}}⟩` is its
associated phase state as defined in Definition 4.9".

A predicate `Γ(z, x)` on pairs of strings is a language `Γ ⊆ {0,1}*` read on the pair encoding
`tup [z, x]`; `predPhaseState Γ z m` is the Boolean phase state of `x ↦ Γ(z, x)` on `m` qubits. -/
noncomputable def predPhaseState (Γ : Set Str) (z : Str) (m : ℕ) : Bits m → ℂ :=
  boolPhaseState (fun x : Bits m => decide (tup [z, x.toStr] ∈ Γ))

end UnitaryQIPPSPACE


