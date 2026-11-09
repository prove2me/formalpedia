-- Prove2me | Definitions.Def_AgnosticTNS_zeroProj
-- name    : AgnosticTNS_zeroProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:16.128223+00:00
-- url     : https://prove2.me/theorems/0e352645-a549-48bb-bbbd-9c692aa15133
-- title:
--   Projector $|0\rangle\langle0|_Q\otimes I$
-- statement:
--   For $Q\subseteq[n]$, the projector $|0^{|Q|}\rangle\langle0^{|Q|}|_Q\otimes I_{[n]\setminus Q}$: the diagonal projector onto the computational basis states whose labels on $Q$ are all $0$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Algorithm 1 line 14, p.19

import Mathlib

namespace AgnosticTNS

/-- **The projector `|0^{|Q|}⟩⟨0^{|Q|}|_Q ⊗ I_{[n]∖Q}`**, Algorithm 1 line 14, p.19 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the
diagonal `n`-qudit projector onto the configurations whose labels on `Q` are all `0`. -/
def zeroProj {n d : ℕ} (Q : Finset (Fin n)) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.diagonal fun x => if ∀ q ∈ Q, (x q : ℕ) = 0 then 1 else 0

end AgnosticTNS


