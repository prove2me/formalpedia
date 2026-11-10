-- Prove2me | Definitions.Def_PPSLattice_garbRun
-- name    : PPSLattice_garbRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:35.891391+00:00
-- url     : https://prove2.me/theorems/699ade04-79c8-4f4e-8501-418d9ed7ec24
-- title:
--   Interaction of an adversary with the garbling challenger
-- statement:
--   In every phase, an oracle query on a circuit of size at most $s$ is answered with $\mathrm{CircGarb}(\mathrm{gk},C)$. First the adversary names $x\in\{0,1\}^\ell$ and receives $\tilde x=\mathrm{InpGarb}(\mathrm{gk},x)$; then it names a circuit $C$ of size at most $s$ and receives $\tilde C\leftarrow\mathrm{CircGarb}(\mathrm{gk},C)$ if $b=0$ or $\tilde C\leftarrow\mathrm{Sim}(\mathrm{gk},x,C(x))$ if $b=1$; then it guesses. Any other move (a second challenge, a malformed challenge, an early guess) or running out of activations ends the run with a uniformly random guess, which enforces "at most one challenge input garbling and challenge circuit garbling queries".
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.4, Security, p.20

import Mathlib
import Definitions.Def_RestrictedDec_Adversary
import Definitions.Def_PPSLattice_Garb
import Definitions.Def_PPSLattice_decGMove
import Definitions.Def_PPSLattice_circSize
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace PPSLattice

/-- The **interaction of an adversary with the garbling challenger** for key `gk` and challenge bit
`b`, for at most `fuel` activations; `ph` is the phase (`0` before the challenge input, `1` after
`x̃`, `2` after `C̃`) and `x` the challenge input. The result is the guess `b′`.
1. In every phase, an oracle query on a circuit `C` with `size C ≤ s` is answered with
   `CircGarb(gk, C)`; other queries get the empty string.
2. In phase `0`, an input `x ∈ {0,1}^ℓ` is answered with `x̃ = InpGarb(gk, x)`.
3. In phase `1`, a circuit `C` with `size C ≤ s` is answered with `C̃ ← CircGarb(gk, C)` if `b = 0`
   and `C̃ ← Sim(gk, x, C(x))` if `b = 1`.
4. In phase `2`, a guess ends the run.
5. Any other move (a second challenge, a malformed challenge, a guess before `C̃`) or running out of
   activations ends the run with a uniformly random guess.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.4, Security, p.20 ("A stateful PPT machine A is said to be admissible if it makes at
most one challenge input garbling and challenge circuit garbling queries"). -/
noncomputable def garbRun (G : Garb) (A : RestrictedDec.Adversary) (lam s ell : ℕ) (gk : Str)
    (b : Bool) : ℕ → ℕ → Str → Str → Str → PMF Bool
  | 0, _, _, _, _ => PMF.uniformOfFintype Bool
  | fuel + 1, ph, x, st, input =>
    (A.activate lam st input).bind fun r =>
      match decGMove r.2 with
      | .query (some C) =>
        if circSize C ≤ s then
          (G.circGarb gk C).bind fun Ct => garbRun G A lam s ell gk b fuel ph x r.1 Ct
        else garbRun G A lam s ell gk b fuel ph x r.1 []
      | .query none => garbRun G A lam s ell gk b fuel ph x r.1 []
      | .input x' =>
        if ph = 0 ∧ x'.length = ell then
          garbRun G A lam s ell gk b fuel 1 x' r.1 (G.inpGarb gk x')
        else PMF.uniformOfFintype Bool
      | .circ (some C) =>
        if ph = 1 ∧ circSize C ≤ s then
          (if b then G.sim gk x (C.eval x) else G.circGarb gk C).bind fun Ct =>
            garbRun G A lam s ell gk b fuel 2 x r.1 Ct
        else PMF.uniformOfFintype Bool
      | .circ none => PMF.uniformOfFintype Bool
      | .guess b' => if ph = 2 then PMF.pure b' else PMF.uniformOfFintype Bool

end PPSLattice


