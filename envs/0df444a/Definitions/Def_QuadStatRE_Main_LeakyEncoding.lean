-- Prove2me | Definitions.Def_QuadStatRE_Main_LeakyEncoding
-- name    : QuadStatRE_Main_LeakyEncoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:44:26.452917+00:00
-- url     : https://prove2.me/theorems/aeb9fcaa-495c-424c-9b6c-5ecd51edd12c
-- title:
--   Encodings with leakage (Definition 2.3) and ZPP-decoders (Definition 2.5)
-- statement:
--   Let $\mathrm{Enc}:X\times R\to Z$ be an encoder of $g:X\to Y$ with a uniform random tape $r\in R$ ($R$, $Z$ finite).
--
--   **Encoding with leakage** (Definition 2.3, p. 13). Let $L(v)$ be a distribution on a finite leakage alphabet $\Lambda$ for every input $v$. The encoding has leakage $L(v)$ with simulation error $\varepsilon$ if there is a randomized algorithm $\mathrm{Sim}_{\mathrm{leak}}$ such that for every input $v$
--   $$\mathrm{SD}\big(\mathrm{Enc}(v),\ \mathrm{Sim}_{\mathrm{leak}}(g(v),L(v))\big)\le\varepsilon,$$
--   where the leakage sample is independent of the simulator's internal randomness. Here the simulator is a deterministic map of $(g(v),\ell,c)$ with $\ell\leftarrow L(v)$ and $c$ a string of $\tau$ uniform coin bits, so its output law is $z\mapsto\sum_{\ell}L(v)(\ell)\Pr_c[\mathrm{Sim}(g(v),\ell,c)=z]$. With $\varepsilon=0$ the encoding "has leakage $L(v)$".
--
--   **ZPP-decoder** (Definition 2.5, p. 14). A decoder $\mathrm{Dec}:Z\to Y\cup\{\bot\}$ is a ZPP-decoder with failure probability at most $\delta$ if it never errs, $\mathrm{Dec}(\mathrm{Enc}(v;r))\in\{g(v),\bot\}$ for every $v$ and every tape $r$, and $\Pr_r[\mathrm{Dec}(\mathrm{Enc}(v;r))=\bot]\le\delta$ for every $v$.
--
--   Leakage is the relaxation of privacy that drives the construction: the basic gadget leaks only an equality test, and the RM step transforms the leakage family in a way the $\chi^2$ analysis can track.
--
--   **Formalization Note.** $\bot$ is `none`; distributions are nonnegative real functions of total mass one; $\mathrm{SD}$ and probabilities over uniform tapes are the published `QuadraticRE.SD`, `law`, `prob`.
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), pp. 13–14, Definitions 2.3 and 2.5

import Mathlib
import Definitions.Def_QuadraticRE_SD

namespace QuadStatRE.Main

open QuadraticRE

/-- Encoding with leakage, Definition 2.3 of Applebaum, *Quadratic Statistical Randomized Encoding
for All Functions*, STOC 2027 submission, p. 13: the encoder `enc : X → R → Z` (uniform tape `r ∈ R`)
of `g : X → Y` has leakage `L(v)` with simulation error `ε` if "there is a randomized algorithm
`Sim_leak` such that, for every input `v`, `SD(Enc(v), Sim_leak(g(v), L(v))) ≤ ε`, where the leakage
sample is independent of the simulator's internal randomness".

`L v` is a distribution on a finite leakage alphabet `Λ`. The simulator is a deterministic map of
`(g v, leakage sample, coins)` with `τ` uniform coin bits; its output law is the mixture
`z ↦ ∑_l L v l · Pr_c[sim (g v) l c = z]`. With `ε = 0` the encoding "has leakage `L(v)`". -/
def HasLeakage {X Y R Z Λ : Type} [Fintype R] [Fintype Z] [Fintype Λ]
    (g : X → Y) (enc : X → R → Z) (L : X → Λ → ℝ) (ε : ℝ) : Prop :=
  (∀ v, IsLaw (L v)) ∧
    ∃ (τ : ℕ) (sim : Y → Λ → (Fin τ → F2) → Z),
      ∀ v, SD (law (enc v)) (fun z => ∑ l, L v l * law (sim (g v) l) z) ≤ ε

/-- ZPP-decoder, Definition 2.5, p. 14: "the decoder may output `⊥` but never an incorrect value:
for every input `v` and every encoder random tape `r`, `Dec(Enc(v; r)) ∈ {g(v), ⊥}`, and
`Pr_r[Dec(Enc(v; r)) = ⊥] ≤ ε_cor`". `none` is `⊥`. -/
def IsZPPDecoder {X Y R Z : Type} [Fintype R]
    (g : X → Y) (enc : X → R → Z) (δ : ℝ) (dec : Z → Option Y) : Prop :=
  (∀ v r, dec (enc v r) = some (g v) ∨ dec (enc v r) = none) ∧
    ∀ v, prob (fun r : R => dec (enc v r) = none) ≤ δ

end QuadStatRE.Main


