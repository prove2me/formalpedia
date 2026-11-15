-- Prove2me | Definitions.Def_SymmetricPSM1041_ORLowerBound_Supplement_ExplicitFunctions
-- name    : SymmetricPSM1041_ORLowerBound_Supplement_ExplicitFunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:44:18.215426+00:00
-- url     : https://prove2.me/theorems/ad0f1105-a40d-424c-a010-8f8741d26d1e
-- title:
--   §2 — majority, exact majority and modular counting
-- statement:
--   For $x\in\{0,1\}^n$ let $\|x\|$ be its Hamming weight, the number of coordinates equal to $1$. The three explicit symmetric functions of the paper are
--
--   $$\mathrm{MAJ}_n(x)=\mathbf 1\bigl[\|x\|\ge n/2\bigr],\qquad \mathrm{EMAJ}_n(x)=\mathbf 1\bigl[\|x\|=\lfloor n/2\rfloor\bigr],\qquad \mathrm{MOD}_{q,n}(x)=\mathbf 1\bigl[\|x\|\equiv0\pmod q\bigr].$$
--
--   They are the targets of the lower bounds for majority and its relatives and of the matching protocols.
--
--   **Formalization Note** Inputs are `Fin n → Bool`; the Hamming weight is the published `ShallowSym.weight`. The majority comparison $\|x\|\ge n/2$ is over the reals and is written $n\le2\|x\|$ in natural numbers. $\mathrm{MOD}_{q,n}$ tests $\|x\| \bmod q=0$, which is divisibility by $q$ for every $q\ge1$; the paper uses only $q\ge2$.
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 6, §2 (the explicit functions MAJ_n, MOD_{q,n}, EMAJ_n)

import Mathlib
import Definitions.Def_ShallowSym_weight

namespace SymmetricPSM1041.ORLowerBound.Supplement

/-- Majority: `MAJ_n(x) = 1[‖x‖ ≥ n/2]`, compared over the reals, i.e. `n ≤ 2‖x‖`. -/
def majFunction (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide (n ≤ 2 * ShallowSym.weight x)

/-- Exact majority: `EMAJ_n(x) = 1[‖x‖ = ⌊n/2⌋]`. -/
def emajFunction (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide (ShallowSym.weight x = n / 2)

/-- Modular counting: `MOD_{q,n}(x) = 1[‖x‖ ≡ 0 (mod q)]`. -/
def modFunction (q n : ℕ) (x : Fin n → Bool) : Bool :=
  decide (ShallowSym.weight x % q = 0)

end SymmetricPSM1041.ORLowerBound.Supplement


