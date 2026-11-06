-- Prove2me | Definitions.Def_ReserveLB_coinSizeExpect
-- name    : ReserveLB_coinSizeExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:41.20754+00:00
-- url     : https://prove2.me/theorems/27288cb6-3bc0-4c80-a698-4bbb35e27148
-- title:
--   Expectation over construction coins and sizes
-- statement:
--   Let $p$ be a polynomial and $N = p(|\mathrm{enc}(I)|)$ for an instance $I$. For a quantity $G(w, x)$ depending on a coin string $w \in \{0,1\}^N$ and the realized size list $x$,
--   $$
--   \mathbb E_{\Sigma, X}\, G = \frac{1}{2^N}\sum_{w \in \{0,1\}^N}\ \sum_{c}\Bigl(\prod_j p_{j c_j}\Bigr) G\bigl(w, (a_{1 c_1}, \dots, a_{n c_n})\bigr),
--   $$
--   where the coins are uniform and the sizes are independent of the coins and of each other, with the listed laws.
--
--   This is the expectation $\mathbb E_{\Sigma, X}$ of Theorem 1.1: "one physical maximum over graph coins and original sizes", with construction coins independent of future sizes.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_ReserveLB_Inst
import Definitions.Def_ReserveLB_encInst

namespace ReserveLB

/-- **Expectation over construction coins and sizes.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Theorem 1.1, p.2: "E_(Σ,X) ms_decoder(Σ, X)"; "the expectation is one physical maximum
over graph coins and original sizes, not a pathwise ratio"; "Construction coins are independent of
future sizes".

For an instance `I`, a polynomial `p` and a quantity `G(w, x)` depending on a coin string `w` and the
realized size list `x`, `coinSizeExpect I p G` averages `G` over all `2^N` coin strings of length
`N = p(|encInst I|)`, uniformly, and over the sizes, independent across jobs with the listed laws
and independent of the coins.

**Formalization Note.** The coins are uniform on `{0,1}^N`, the sizes have the exact product law
(a finite sum over one listed atom per job); the size list has the size of job `j` at position `j`. -/
noncomputable def coinSizeExpect (I : Inst) (p : Polynomial ℕ) (G : List Bool → List ℚ → ℝ) : ℝ :=
  (1 / 2 ^ (p.eval (encInst I).length) : ℝ) *
    ∑ w : Fin (p.eval (encInst I).length) → Bool,
      ∑ c : (j : Fin I.laws.length) → Fin (I.laws.get j).length,
        (∏ j, ((((I.laws.get j).get (c j)).2 : ℚ) : ℝ)) *
          G (List.ofFn w) (List.ofFn fun j => ((I.laws.get j).get (c j)).1)

end ReserveLB


