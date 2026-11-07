-- Prove2me | Definitions.Def_PCNonBool_IsRun
-- name    : PCNonBool_IsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:36:37.75059+00:00
-- url     : https://prove2.me/theorems/4f363e1c-a84c-4f7b-8881-8052053d5798
-- title:
--   A run of Algorithm 1
-- statement:
--   A **run** of $L$ rounds of Algorithm 1 on input $(\pi,G,D)$ is a sequence of states $\mathrm{st}_0,\dots,\mathrm{st}_L$ with $\mathrm{st}_0=(\pi,U,V,\emptyset)$ (lines 2–7) and $\mathrm{st}_{\ell+1}$ obtained from $\mathrm{st}_\ell$ by one round. Algorithm 1 itself runs $L=\lfloor\tau\rfloor$ rounds.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Algorithm 1 (lines 2–9), p.30 (PDF p.33)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_AlgState
import Definitions.Def_PCNonBool_Step

namespace PCNonBool

/-- `st` is a run of `L` rounds of Algorithm 1 on input `(π, G, D)` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.30 (PDF p.33)):
it starts from `π_0 = π`, `U_0 = U`, `V_0 = V`, `C_0 = ∅` (lines 2–7) and consecutive states are
related by one round (`Step`). The full algorithm runs `L = ⌊τ⌋` rounds. -/
def IsRun {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U]
    [DecidableEq V] (G : BipGraph U V) (s : ℕ) (c D : ℝ) (π : List (MvPolynomial (Var G) F))
    (L : ℕ) (st : ℕ → AlgState (F := F) G) : Prop :=
  st 0 = ⟨π, Finset.univ, Finset.univ, ∅⟩ ∧ ∀ ℓ < L, Step G s c D (st ℓ) (st (ℓ + 1))

end PCNonBool


