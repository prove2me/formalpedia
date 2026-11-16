-- Prove2me | Definitions.Def_CEPolytopeHard_Supplement_quadCEProblem
-- name    : CEPolytopeHard_Supplement_quadCEProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:11:47.895268+00:00
-- url     : https://prove2.me/theorems/f48f1874-bac9-4a8e-baf1-137ce0f1145c
-- title:
--   Search problem: a $d^{-c}$-correlated equilibrium with at most $d^C$ profiles in a two-player quadratic concave game
-- statement:
--   Fix reals $C$, $c$. The search problem $\mathrm{QuadCE}(C,c)$ is the following.
--
--   1. **Instance.** The binary code of a dimension $d\ge1$ and two valid well-behaved arithmetic circuits $U_1,U_2$ with $2d$ inputs and one output, such that the utilities $u_i(x,y)=U_i(x,y)$ agree on $[0,1]^d\times[0,1]^d$ with those of a valid two-player quadratic concave game (values in $[0,1]$, concave quadratic in the player's own strategy, continuous).
--   2. **Answer.** The code of a list of pairs $(w,(x,y))$ of a rational weight $w\ge0$ and a rational profile in $\mathbb Q^d\times\mathbb Q^d$, with $\sum w=1$, whose distribution $\mu$ (equal profiles merged) is supported in $[0,1]^d\times[0,1]^d$, has at most $d^C$ support profiles, and is a $d^{-c}$-**correlated equilibrium**: for each player $i$ and every map $\phi:[0,1]^d\to[0,1]^d$,
--   $$\mathbb E_{(x_1,x_2)\sim\mu}\big[u_i(\phi(x_i),x_{-i})-u_i(x_1,x_2)\big]\le d^{-c}.$$
--
--   This is the problem whose PPAD-hardness is Theorem 2.
--
--   **Formalization Note** The answer code is the mission's `encodeDist`; $d^C$, $d^{-c}$ are real powers.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Theorem 2, p.5; Section 2.3, p.11; Section 2.1, p.10

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_NadlerCLS_Circ
import Definitions.Def_CEPolytopeHard_IsApproxCE
import Definitions.Def_CEPolytopeHard_encodeDist
import Definitions.Def_CEPolytopeHard_Supplement_QuadGame
import Definitions.Def_CEPolytopeHard_Supplement_fixedSetProblem

set_option autoImplicit false

namespace CEPolytopeHard.Supplement

open NetworkEquilibriumCLS.LinearNash

/-- the utility on profiles `(x, y) ∈ ℝ^d × ℝ^d` computed by a circuit with `2d` inputs (the
coordinates of `x`, then those of `y`) and one output (raw value) -/
noncomputable def circUtil (d : ℕ) (U : NadlerCLS.Circ) (p : Fin 2 → Fin d → ℝ) : ℝ :=
  U.eval (ins := d + d) (outs := 1) (Fin.append (p 0) (p 1)) 0

/-- the real two-player profile of a listed rational profile `[x, y]` (missing entries `0`) -/
def twoProfile (d : ℕ) (p : List (List ℚ)) : Fin 2 → Fin d → ℝ :=
  fun i => ratVec d (p.getD i.val [])

/-- the distribution listed by `L`: weights of equal profiles are merged (summed) -/
noncomputable def twoDist (d : ℕ) (L : List (ℚ × List (List ℚ))) :
    (Fin 2 → Fin d → ℝ) →₀ ℝ :=
  (L.map fun e => Finsupp.single (twoProfile d e.2) (e.1 : ℝ)).sum

/-- The **search problem of computing a `d^{−c}`-correlated equilibrium supported on at most
`d^C` profiles in a two-player quadratic concave game on `[0,1]^d`**
(Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria
Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256
6aec500a…7820, Theorem 2, p.5: "computing a d^{−c}-correlated equilibrium supported on at most d^C
strategy profiles … in two-player concave games with X_1 = X_2 = [0, 1]^d where each utility is
quadratic in the player’s own strategy"; Section 2.1, p.10, for the representation).

* An instance is the code `encNat d ++ encCirc U₁ ++ encCirc U₂` of a dimension `d ≥ 1` and two
  valid well-behaved circuits with `2d` inputs and one output whose utilities `u₁, u₂`
  coincide on `[0,1]^d × [0,1]^d` with those of a valid quadratic concave game (`QuadGame.Valid`:
  values in `[0,1]`, concave quadratic in the own strategy, continuous).
* An answer is the code (`encodeDist`) of a list of pairs `(w, [x, y])` of a rational weight and
  two rational vectors of length `d`, with every `w ≥ 0` and `∑ w = 1`, such that the listed
  distribution (equal profiles merged) is a `d^{−c}`-correlated equilibrium (every deviation map
  `[0,1]^d → [0,1]^d`, `IsApproxCE`) whose support has at most `d^C` profiles.

**Formalization Note** `C`, `c` are real; `d^C`, `d^{−c}` are real powers. -/
noncomputable def quadCEProblem (C c : ℝ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (d : ℕ) (U₁ U₂ : NadlerCLS.Circ),
    encNat d ++ NadlerCLS.encCirc U₁ ++ NadlerCLS.encCirc U₂ = s ∧ 0 < d ∧
    U₁.Valid (d + d) 1 ∧ U₂.Valid (d + d) 1 ∧
    ∃ G : QuadGame d, G.Valid ∧ ∀ p : Fin 2 → Fin d → ℝ, (∀ j, p j ∈ box d) →
      circUtil d U₁ p = G.utility 0 p ∧ circUtil d U₂ p = G.utility 1 p
  answer s t := ∃ (d : ℕ) (U₁ U₂ : NadlerCLS.Circ),
    encNat d ++ NadlerCLS.encCirc U₁ ++ NadlerCLS.encCirc U₂ = s ∧ 0 < d ∧
    U₁.Valid (d + d) 1 ∧ U₂.Valid (d + d) 1 ∧
    (∃ G : QuadGame d, G.Valid ∧ ∀ p : Fin 2 → Fin d → ℝ, (∀ j, p j ∈ box d) →
      circUtil d U₁ p = G.utility 0 p ∧ circUtil d U₂ p = G.utility 1 p) ∧
    ∃ L : List (ℚ × List (List ℚ)), encodeDist L = t ∧
      (∀ e ∈ L, e.2.length = 2 ∧ ∀ v ∈ e.2, v.length = d) ∧
      (∀ e ∈ L, 0 ≤ e.1) ∧ (L.map Prod.fst).sum = 1 ∧
      IsApproxCE (E := fun _ : Fin 2 => Fin d → ℝ) (fun _ => box d)
        ![circUtil d U₁, circUtil d U₂] ((d : ℝ) ^ (-c)) (twoDist d L) ∧
      ((twoDist d L).support.card : ℝ) ≤ (d : ℝ) ^ C

end CEPolytopeHard.Supplement


