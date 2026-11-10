-- Prove2me | Definitions.Def_PPSLattice_SEPRF_IsSEPRF
-- name    : PPSLattice_SEPRF_IsSEPRF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:35:14.125194+00:00
-- url     : https://prove2.me/theorems/eac010b5-fd00-4890-80a2-b243542f31c6
-- title:
--   Somewhere equivocal PRF: Definition 4.2
-- statement:
--   An SEPRF scheme is a **somewhere equivocal PRF** if, for every $\lambda\ge1$ (§3: $\mathbb N$ is the set of positive integers) and every $\ell_{\mathrm{out}}\ge1$:
--
--   1. (syntax) every key output by Setup or by Sim2 evaluates every $x\in\{0,1\}^\lambda$ to a string of length $\ell_{\mathrm{out}}$;
--   2. (correctness) for every $x^*\in\{0,1\}^\lambda$, $y^*\in\{0,1\}^{\ell_{\mathrm{out}}}$, every $\mathrm{eqKey}$ output by $\mathrm{Sim1}(1^\lambda,1^{\ell_{\mathrm{out}}},x^*)$ and every $\mathrm{key}$ output by $\mathrm{Sim2}(\mathrm{eqKey},y^*)$: $\mathrm{Eval}(\mathrm{key},x)=\mathrm{Eval}(\mathrm{eqKey},x)$ for every $x\in\{0,1\}^\lambda$ with $x\ne x^*$, and $\mathrm{Eval}(\mathrm{key},x^*)=y^*$;
--   3. (security) every PPT adversary has negligible advantage $|\Pr[\text{SEPRF experiment}=1]-\tfrac12|$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.2, p.19; §4.2, p.19

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_PPSLattice_seprfGame
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- An SEPRF scheme is a **somewhere equivocal PRF** (Definition 4.2), for every output size
`ℓ_out ≥ 1`:
1. (syntax) every key output by Setup or by Sim2 evaluates every `x ∈ {0,1}^λ` to a string of
   length `ℓ_out`;
2. (correctness) for `x* ∈ {0,1}^λ`, `y* ∈ {0,1}^{ℓ_out}`, every `eqKey` output by
   `Sim1(1^λ, 1^{ℓ_out}, x*)` and every `key` output by `Sim2(eqKey, y*)`: `Eval(key, x) = Eval(eqKey, x)`
   for every `x ∈ {0,1}^λ` with `x ≠ x*`, and `Eval(key, x*) = y*`;
3. (security) every uniform PPT adversary has negligible advantage `|Pr[seprfGame = 1] − ½|`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.2, p.19; syntax of Eval, p.19 ("outputs value y ∈ {0,1}^ℓ").

**Formalization Note.** The syntax and correctness clauses are stated for `λ ≥ 1`, since `λ ∈ N` ranges over the positive integers (§3, p.15: "We denote … the set of positive integers by N"). Correctness is required for every possible output of Sim1 and Sim2
(probability one). The output-length clause is the syntax of Eval (p.19), stated for the keys the
scheme produces. -/
def SEPRF.IsSEPRF (F : SEPRF) : Prop :=
  (∀ lam lo : ℕ, 1 ≤ lam → 1 ≤ lo → ∀ key ∈ (F.setup lam lo).support, ∀ x : Str, x.length = lam →
      (F.eval key x).length = lo) ∧
    (∀ lam lo : ℕ, 1 ≤ lam → 1 ≤ lo → ∀ xs : Str, xs.length = lam → ∀ ys : Str, ys.length = lo →
      ∀ ek ∈ (F.sim1 lam lo xs).support, ∀ key ∈ (F.sim2 ek ys).support,
        (∀ x : Str, x.length = lam → x ≠ xs → F.eval key x = F.eval ek x) ∧
          F.eval key xs = ys ∧ ∀ x : Str, x.length = lam → (F.eval key x).length = lo) ∧
    ∀ A : RestrictedDec.Adversary, A.Valid →
      NoisyOWMPC.Negligible fun lam => |((seprfGame F A lam) true).toReal - 1 / 2|

end PPSLattice


