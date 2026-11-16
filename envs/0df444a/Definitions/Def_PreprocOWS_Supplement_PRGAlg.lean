-- Prove2me | Definitions.Def_PreprocOWS_Supplement_PRGAlg
-- name    : PreprocOWS_Supplement_PRGAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:10:45.617211+00:00
-- url     : https://prove2.me/theorems/0660faad-6983-4dfa-99d5-f25c8161f05a
-- title:
--   $T$-query PRG adversary and its run $A_R=(O_RU)^T$
-- statement:
--   In the PRG game the random oracle is a function $R:[N]\to[M]$ with $M = 2^m$, i.e. $R:[N]\to\{0,1\}^m$, uniform over all $M^N$ functions. For bit strings, $u\cdot y\in\mathbb F_2$ is the inner product.
--
--   A **$T$-query PRG adversary** acts on the basis $[2^S]\times\{0,1\}^m\times[2^w]$ (an $S$-qubit advice register, the challenge register and a $w$-qubit workspace) and consists of
--
--   1. a query map $q$ assigning to each basis state $s$ either nothing or a pair $(x,u)\in[N]\times\{0,1\}^m$; a query applies the phase $O_R|s\rangle = (-1)^{u\cdot R(x)}|s\rangle$ (and $1$ when $q(s)$ is empty);
--   2. unitaries $U_1,\dots,U_T$, giving the run $A_R = O_RU_T\cdots O_RU_1$;
--   3. a final distinguishing measurement operator $\Pi$ (guess $b=0$).
--
--   The query map, the unitaries and $\Pi$ are fixed before $R$.
--
--   **Formalization Note** The page's oracle is the standard oracle $|x,y\rangle\mapsto|x,y\oplus R(x)\rangle$. It equals the phase oracle $(-1)^{u\cdot R(x)}$ conjugated by Hadamards on the output register, and the Hadamards are absorbed into the neighbouring unitaries and $\Pi$. A general query map and distinct $U_i$ contain this form.
-- source:
--   Dong, Lombardi, Lower Bounds for Preprocessing Attacks on Quantum Cryptography, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…), Definition 8.1, p.30 (PDF p.33); §8.1, p.31 (PDF p.34); §3.1, p.11 (PDF p.14)

import Mathlib
import Definitions.Def_PreprocOWS_Oracle
import Definitions.Def_PreprocOWS_Alg
open Matrix

namespace PreprocOWS.Supplement

open PreprocOWS

/-- The **PRG random oracle** `R : [N] → [M]` with `M = 2^m`, i.e. `R : [N] → {0,1}^m`, of the PRG
security game, Dong–Lombardi, arXiv:2610.02101 (version of 2026-11-02, sha256 7a0bd8da…),
Definition 8.1, p.30 (PDF p.33); §3, p.11 (PDF p.14: "`M = 2^m`", XOR oracle on bit strings).

**Formalization Note.** `[N]` is relabelled `Fin N`; the range `[M]` is the set of bit strings
`Fin m → Bool` (the page's challenge preparation `H|y⟩` and phases `(−1)^{y·R(x)}`, §8.1, p.31, use
bit strings). "`R` is sampled" is the uniform average over all `M^N` functions (`PreprocOWS.avg`). -/
abbrev PRGOracle (N m : ℕ) : Type := Fin N → (Fin m → Bool)

/-- The inner product `u · y ∈ F₂` of two bit strings (arXiv:2610.02101, §3, p.11: "`x · y` … taken
over `F₂^n`"), as a bit. -/
def bitDot {m : ℕ} (u y : Fin m → Bool) : Bool :=
  decide (Odd (Finset.univ.filter fun i => u i && y i).card)

/-- The computational basis `Ω = [2^S] × {0,1}^m × [2^w]` of a PRG adversary: the `S`-qubit advice
register, the challenge register (holding `y ∈ [M]`) and the `w`-qubit workspace (arXiv:2610.02101,
§8.1, p.31, PDF p.34). -/
abbrev ΩP (S m w : ℕ) : Type := Fin (2 ^ S) × (Fin m → Bool) × Fin (2 ^ w)

/-- A **`T`-query PRG adversary** (arXiv:2610.02101, Definition 8.1, p.30; §8.1, p.31; §3.1, p.11):
* `q s ∈ Option ([N] × {0,1}^m)` is the query read on basis state `s` (`none`: no query on `s`); a
  query applies the phase `O_R |s⟩ = (−1)^{u · R(x)} |s⟩` for `q s = some (x, u)`;
* `U i` is the unitary applied before the `(i+1)`-st query; the run is `A_R = O_R U_T ⋯ O_R U_1`;
* `meas` is the final distinguishing measurement `Π` (guess "`b = 0`"), with `0 ⪯ Π ⪯ I`.

**Formalization Note.** The page's oracle is the standard oracle `O_R|x,y⟩ = |x, y ⊕ R(x)⟩` and one
unitary `U` between queries. The standard oracle is the phase oracle `(−1)^{u·R(x)}` conjugated by
Hadamards on the output register, and the Hadamards are absorbed into the neighbouring unitaries and
into `Π`; a general query map and distinct `U_i` include this form. A final unitary is absorbed into
`Π`. Only `R` is random: `q`, `U`, `meas` are fixed before `R`. -/
structure PRGAlg (S T N m w : ℕ) where
  q : ΩP S m w → Option (Fin N × (Fin m → Bool))
  U : Fin T → Matrix.unitaryGroup (ΩP S m w) ℂ
  meas : Matrix (ΩP S m w) (ΩP S m w) ℂ

/-- The phase `(−1)^{u·R(x)}` of an optional query (`1` for `none`). -/
def prgOptSgn {N m : ℕ} (R : PRGOracle N m) : Option (Fin N × (Fin m → Bool)) → ℂ
  | none => 1
  | some (x, u) => sgn (bitDot u (R x))

/-- The run `A_R = (O_R U)^T = O_R U_T ⋯ O_R U_1` of a PRG adversary (arXiv:2610.02101, §8.1, p.31,
PDF p.34), with `O_R` the diagonal phase oracle of the query map. -/
def prgRun {S T N m w : ℕ} (A : PRGAlg S T N m w) (R : PRGOracle N m) :
    Matrix (ΩP S m w) (ΩP S m w) ℂ :=
  layeredRun (Matrix.diagonal fun s => prgOptSgn R (A.q s))
    (fun i => (A.U i : Matrix (ΩP S m w) (ΩP S m w) ℂ))

end PreprocOWS.Supplement


