-- Prove2me | Definitions.Def_PopRAM_PProgram
-- name    : PopRAM_PProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:36.180206+00:00
-- url     : https://prove2.me/theorems/d2db799c-3810-49b9-a18b-617b67f59de6
-- title:
--   $\mathcal P$-programs (Definition 1) and the population size $n_w$
-- statement:
--   A **$\mathcal P$-program** is a family of $w$-RAM programs, one for each word length $w$, of uniformly bounded length, together with functions $T_R, T_{RAM}, T_P, \rho$ of the word length $w$ and, for every $w$, a set of **admissible** input tuples $k=(k_1,\dots,k_{T_R(w)})$ with every $k_i<2^{w-1}$, such that
--
--   1. $T = T_R + T_{RAM} + T_P$ is bounded by a polynomial in $w$;
--   2. $\rho = O(T)$;
--   3. $T_{RAM}\ge 1$;
--   4. for some $w_1$ and all $w\ge w_1$: on every admissible tuple $k$, and on every tuple $k'\le k$ (coordinatewise), the program with $\rho(w)$ registers runs without fault, halts, executes exactly $T_R(w)$ READs, at most $T_{RAM}(w)$ RAM instructions and exactly $T_P(w)$ PRINTs, and prints only values in $[0,2^{w-1})$.
--
--   The paper says the program has fixed length (p.7) and encodes its code, constants and direct addresses in the transition function; here those may depend on $w$, and one program independent of $w$ is the constant family. The tuples $k'\le k$ are the "partial input counts used during backup retries" to which Definition 1 also applies.
--
--   Derived quantities: $\rho' = \rho + T_R + T_P + 4$ (registers of the simulation: the input array, the output array and four auxiliary registers), the **population size**
--   $$n_w = C\bigl((T_R+T_P+1)2^w + \rho' w\bigr)$$
--   for an integer constant $C>1$, and $S = T_R w + T_{RAM} + T_P$, the factor in the paper's bounds. $\mathrm{out}_w(k)_j$ is the $j$-th printed value on input $k$.
--
--   **Formalization Note** The paper's $\rho'=\rho+T_R+T_P+O(1)$ fixes the $O(1)$ to $4$ ($r_{p}^{in}$, $r_{p}^{out}$, $r_c$ and one spare). Requirement 4 is asked only from some $w_1$ on, since the theorems are claimed "for all sufficiently large $w$" and short words cannot hold $\rho$ addresses.
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Definition 1, pp.5–6 (PDF pp.6–7); population size, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_PopRAM_WordRAM

set_option autoImplicit false

namespace PopRAM

/-! # P-programs (Definition 1) and the population size `n_w`

Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by Population Protocols*,
arXiv:2611.06178 (held version, sha256 f13223b3…), Definition 1, pp.5–6 (PDF pp.6–7), and
"Population size and data representation", p.6 (PDF p.7).

**Formalization Note**
- A P-program has an instruction list `code w` for each word length `w`, of **uniformly bounded
  length** (`code_len`; p.7: "The simulated P-program has fixed length"; its code, "including
  constants and direct register addresses, is encoded in the transition function"). The constants,
  jump targets and direct addresses may depend on `w`; one program independent of `w` is the constant
  family. With it come the resource functions `TR`, `TRAM`, `TP`, `rho` of `w` and, for each `w`, the set `adm w` of
  admissible input tuples `k : Fin (TR w) → ℕ`, each value `< 2^(w-1)` ("each input and output value
  is a non-negative (w − 1)-bit integer", p.5).
- `poly`: `TR + TRAM + TP = poly(w)`; `rho_le`: `ρ = O(T)`; `tram_pos`: `TRAM ≥ 1` (p.6, "We take
  TRAM ≥ 1, increasing this upper bound if necessary").
- `good`: items 1, 3 and 4 of Definition 1 (`Behaves`) hold on every admissible tuple **and on every
  pointwise smaller tuple** `k' ≤ k`. This encodes "These requirements also apply to the partial input
  counts used during backup retries" (p.6): a retry runs the program on a partial count of each input.
- `good` is required for all `w ≥ w₁`, for some `w₁`: the theorems of the paper are claimed only "for
  all sufficiently large w", and for small `w` the `ρ` register addresses need not fit in `w`-bit
  words (p.6: "For sufficiently large w, all ρ′ … register addresses fit in non-negative w-bit
  words").
- `rho' w = ρ + TR + TP + 4`: the paper's `ρ′ = ρ + TR + TP + O(1)` with the `O(1)` auxiliary
  registers fixed to four (the pointers `rp_in`, `rp_out`, the counter `r_c`, one spare).
- `nPop C w = C((TR + TP + 1)2^w + ρ′w)` is the paper's `n_w`; `S w = TR·w + TRAM + TP` is the
  factor `T_R w + T_RAM + T_P` of the bounds. -/

/-- A P-program (Definition 1). -/
structure PProgram where
  /-- the program at word length `w` -/
  code : ℕ → List Instr
  /-- the program has fixed length: its length is bounded uniformly in `w` -/
  code_len : ∃ L : ℕ, ∀ w, (code w).length ≤ L
  /-- number of executed READ instructions -/
  TR : ℕ → ℕ
  /-- upper bound on the number of executed RAM instructions -/
  TRAM : ℕ → ℕ
  /-- number of executed PRINT instructions -/
  TP : ℕ → ℕ
  /-- number of registers -/
  rho : ℕ → ℕ
  /-- admissible input tuples at word length `w` -/
  adm : (w : ℕ) → Set (Fin (TR w) → ℕ)
  adm_lt : ∀ w, ∀ k ∈ adm w, ∀ i, k i < 2 ^ (w - 1)
  poly : ∃ c : ℕ, ∀ w, TR w + TRAM w + TP w ≤ c * (w + 1) ^ c
  rho_le : ∃ c : ℕ, ∀ w, rho w ≤ c * (TR w + TRAM w + TP w)
  tram_pos : ∀ w, 1 ≤ TRAM w
  good : ∃ w₁ : ℕ, ∀ w ≥ w₁, ∀ k ∈ adm w, ∀ k' : Fin (TR w) → ℕ, k' ≤ k →
    Behaves (code w) w (TR w) (TRAM w) (TP w) (rho w) k'

namespace PProgram

variable (P : PProgram)

/-- `T = TR + TRAM + TP`, the bound on executed instructions. -/
def T (w : ℕ) : ℕ := P.TR w + P.TRAM w + P.TP w

/-- `ρ′ = ρ + TR + TP + 4`: the registers of the simulation (input array, output array, four
auxiliary registers). -/
def rho' (w : ℕ) : ℕ := P.rho w + P.TR w + P.TP w + 4

/-- The population size `n_w = C((TR + TP + 1)2^w + ρ′w)`. -/
def nPop (C w : ℕ) : ℕ := C * ((P.TR w + P.TP w + 1) * 2 ^ w + P.rho' w * w)

/-- The factor `TR·w + TRAM + TP` of the paper's bounds. -/
def S (w : ℕ) : ℕ := P.TR w * w + P.TRAM w + P.TP w

/-- The program's `j`-th output on input `k` at word length `w`. -/
def out (w : ℕ) (k : Fin (P.TR w) → ℕ) (j : Fin (P.TP w)) : ℕ :=
  progOut (P.code w) w (P.rho w) (List.ofFn k) (P.T w) j

end PProgram

end PopRAM


