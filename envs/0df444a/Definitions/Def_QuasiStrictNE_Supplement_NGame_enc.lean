-- Prove2me | Definitions.Def_QuasiStrictNE_Supplement_NGame_enc
-- name    : QuasiStrictNE_Supplement_NGame_enc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:41:52.638619+00:00
-- url     : https://prove2.me/theorems/c3e79a25-6b77-45e3-9ef3-cdd88be40437
-- title:
--   Binary code of an $n$-player strategic-form game
-- statement:
--   The **binary code** of an $n$-player game is $n$ in self-delimiting binary, then the action counts $k_0,\dots,k_{n-1}$ in self-delimiting binary, then, for each player $i = 0,\dots,n-1$ in turn, the payoffs $u_i(s)$ for all pure profiles $s$ in lexicographic order, each written as a reduced fraction (signed binary numerator, binary denominator).
--
--   The input size of a game in Theorem 2 is the length of this code, so the full payoff table counts.
--
--   **Formalization Note** The code uses the platform's public `encBin` and `encRat`. All parts are self-delimiting, and once $n$ and the $k_i$ are read the number of payoff entries is fixed, so a string codes at most one game.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Theorem 2, p.19 ("an n-player game in strategic form with rational payoffs")

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_QuasiStrictNE_Supplement_NGame
import Definitions.Def_QuasiStrictNE_Supplement_profileList

set_option autoImplicit false

namespace QuasiStrictNE.Supplement

open QAlgorithms.LocalHamiltonian

/-- **Binary code of an `n`-player game in strategic form** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Theorem 2, p.19: the input
"n-player game in strategic form with rational payoffs"; its size is the length of this code).

The code is: `n` in self-delimiting binary (`encBin`); the action counts `k 0, …, k (n−1)`, each by
`encBin`; then, for each player `i = 0, …, n−1` in turn, the payoffs `u i s` for every pure profile
`s` in the order of `profileList`, each as a reduced fraction by `encRat`.

**Formalization Note** The paper fixes no encoding. `encBin` and `encRat` are the platform's public
self-delimiting codes, and once `n` and the `k i` are read the number of payoff entries is
determined, so a string is the code of at most one game. The full payoff table is written out
(strategic form, no succinct representation). -/
def NGame.enc {n : ℕ} (G : NGame n) : List Bool :=
  encBin n ++ (List.finRange n).flatMap (fun i => encBin (G.k i)) ++
    (List.finRange n).flatMap (fun i => (profileList n G.k).flatMap (fun s => encRat (G.u i s)))

end QuasiStrictNE.Supplement


