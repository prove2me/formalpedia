-- Prove2me | Definitions.Def_RestrictedDec_Supplement_Simulates
-- name    : RestrictedDec_Supplement_Simulates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:25:26.030491+00:00
-- url     : https://prove2.me/theorems/e2353da3-9d08-4fd1-adaf-b5564c2d4c65
-- title:
--   Oracle simulation $\mathcal F\preceq\mathcal G$ (§3.1)
-- statement:
--   $\mathcal F\preceq\mathcal G$ over $M$ if a uniform PPT simulator, given $1^\lambda$ and a description of $F\in\mathcal F$, and oracle access to $G(x)$ for permitted $G\in\mathcal G$ (all queries at the same point $x$), outputs $F(x)$ except with probability at most $\varepsilon_{\mathrm{sim}}(\lambda)$, where one negligible $\varepsilon_{\mathrm{sim}}$ works for every $\lambda$, every admissible $F$ and every $x\in M_\perp$:
--   $$\Pr[\text{simulator outputs }F(x)]\ \ge\ 1-\varepsilon_{\mathrm{sim}}(\lambda).$$
--
--   Proposition 1 shows $\mathcal F\preceq\mathcal G\Rightarrow\mathrm{Sec}^t(\mathcal G)\subseteq\mathrm{Sec}^t(\mathcal F)$; Theorems 3 and 4 assume this relation between adjacent classes.
--
--   **Formalization Note** The simulator is a `RestrictedDec.Adversary`; inadmissible $\mathcal G$-descriptions are refused.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), §3.1, p.15

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_encOpt
import Definitions.Def_RestrictedDec_Family
import Definitions.Def_RestrictedDec_Adversary
import Definitions.Def_RestrictedDec_Supplement_interact
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- A run of a **same-point simulator** `S` with oracle access to the family `𝓖` at the point
`x ∈ M_⊥`: on a move `tup [0, d′]` the simulator receives `encOpt (some (G_{d′}(x)))` if `d′` is
`𝓖`-admissible and `encOpt none` (refusal) otherwise; a move `tup [1, y]` ends the run with output
`y`. Running out of activations gives no output (`none`). -/
noncomputable def simRun (S : Adversary) (G : Family) (lam : ℕ) (x : Option Str) :
    ℕ → Str → Str → PMF (Option Str)
  | 0, _, _ => PMF.pure none
  | fuel + 1, s, input =>
    (S.activate lam s input).bind fun r =>
      if fld r.2 0 = [false] then
        simRun S G lam x fuel r.1
          (encOpt (if G.admissible lam (fld r.2 1) then some (G.eval lam (fld r.2 1) x) else none))
      else PMF.pure (some (fld r.2 1))

/-- **Oracle simulation** `𝓕 ⪯ 𝓖` over the message space `M`: a uniform PPT simulator, given `1^λ`
and a description `d` of `F ∈ 𝓕`, with oracle access to `G(x)` for permitted `G ∈ 𝓖` (all queries
at the same `x`), outputs `F(x)` except with probability at most `ε_sim(λ)`, for one negligible
`ε_sim`, every `λ`, every admissible `d` and every `x ∈ M_⊥`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), §3.1, p.15 ("Write F ⪯ G if a
uniform polynomial-time algorithm, given a description of F ∈ F and oracle access to G(x) for
permitted G ∈ G, computes F(x) for every x ∈ M⊥. It may make polynomially many queries, all
evaluated at the same x. For a randomized simulator, the error is bounded by one negligible function
εsim(λ), uniformly over x and admissible F.").

**Formalization Note.** The simulator is a `RestrictedDec.Adversary` (uniform reactive machine,
`p(λ)` fresh coins per activation, at most `p(λ) + 1` activations, so polynomially many queries);
its first input is `d`. -/
def Simulates (M : ℕ → Str → Prop) (F G : Family) : Prop :=
  ∃ S : Adversary, S.Valid ∧ ∃ ε : ℕ → ℝ, NoisyOWMPC.Negligible ε ∧
    ∀ (lam : ℕ) (d : Str) (x : Option Str), F.admissible lam d = true →
      (∀ m, x = some m → M lam m) →
      ENNReal.ofReal (1 - ε lam) ≤ simRun S G lam x (S.p.eval lam + 1) [] d (some (F.eval lam d x))

end Supplement

end RestrictedDec


