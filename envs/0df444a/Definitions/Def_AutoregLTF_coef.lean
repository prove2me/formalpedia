-- Prove2me | Definitions.Def_AutoregLTF_coef
-- name    : AutoregLTF_coef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:17.63265+00:00
-- url     : https://prove2.me/theorems/c9af6fdd-af1b-43e2-8ca5-3225732464e7
-- title:
--   The coefficients of Lemma 2: $B=2^{m+5}(m+2)$, $a^{(0)}$ from (17)–(18), and $a$ from (22)–(23)
-- statement:
--   In the proof of Lemma 2, $B=2^{m+5}(m+2)$, and for every $j\in[m]$ the auxiliary coefficients are assigned by
--
--   $$\begin{aligned}
--   &a^{(0)}_{p+\pi(\mathrm{test})-\pi(\mathrm{row},j)}=4\theta_j, &&a^{(0)}_{p+\pi(\mathrm{test})-\pi(\mathrm{out},j)}=-2^{j+1}, &&a^{(0)}_{p+\pi(\mathrm{test})-\pi(\mathrm{ptr},j)}=-2^{j+1},\\
--   &a^{(0)}_{\pi(\mathrm{out},j)-\pi(\mathrm{test})}=1, &&a^{(0)}_{p+\pi(\mathrm{out},j)-\pi(\mathrm{ptr},j)}=1, &&a^{(0)}_{p+\pi(\mathrm{ptr},j)-\pi(\mathrm{ptr},j+1)}=4,
--   \end{aligned}$$
--
--   (17a)–(17f), together with (18): the indices of (17b)–(17f) shifted by $+1$ carry the negated values $2^{j+1},2^{j+1},-1,-1,-4$. All other $a^{(0)}_\ell$, $\ell\in[p+1]$, are $0$. The final $a$ starts from $a^{(0)}$ and is updated by (22): $a_1=2$, $a_{p-1}=1-B$, $a_p=B+1$, $a_{p+1}=-B-1$, $a_{\pi(\mathrm{test})}=B+1$, $a_{\pi(\mathrm{out},j)}=B-2$ ($j\in[m]$), $a_{\pi(\mathrm{ptr},j)}=B-3$ ($j\in[m+1]$), $a_{\pi(b)+1}=B-1$ for every test, output and pointer coordinate $b$; and by (23): $a_\ell=-B^2$ for $p/3<\ell\le2p/3$.
--
--   These are the weights of the single LTF that rewrites a block into the next one.
--
--   **Formalization Note** (17)–(18) and (22)–(23) are explicit lists of (index, value) pairs, `assign0 m θ` and `assignUpd m`, with integer indices. `a0 m θ ℓ` reads the first pair with index $\ell$ (else $0$) and `aCoef m θ ℓ` reads `assignUpd` first, then `a0`. Claim 1 and the disjointness of (22)–(23) are stated on these lists, so the lookup order does not matter.
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), proof of Lemma 2, B, (17)–(18) p.8, (22)–(23) p.9

import Mathlib
import Definitions.Def_AutoregLTF_block

namespace AutoregLTF

/-!
# The coefficients of the proof of Lemma 2: `B`, the assignments (17)–(18) and (22)–(23)

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), proof of Lemma 2,
(17)–(18) p.8 and (22)–(23) p.9.

`B = 2^{m+5}(m + 2)`. The auxiliary vector `a^{(0)}` is given by the assignments (17a)–(17f) and (18)
for every `j ∈ [m]`, and is zero at every other `ℓ ∈ [p + 1]`. The final vector `a` starts from
`a^{(0)}` and is updated at the coordinates of (22) and on the range (23).

**Formalization Note.**
* (17)–(18) and (22)–(23) are written as explicit lists of `(index, value)` pairs, `assign0` and
  `assignUpd`, so that Claim 1 (consistency of (17)–(18)) and the disjointness of (22)–(23) are
  statements about these lists, not consequences of how a function is written. Indices are integers,
  so that `p + π(test) − π(row, j)` and its kin are computed without truncation.
* `a0 m θ ℓ` is the value of the first pair of `assign0` with index `ℓ`, and `0` if there is none;
  `aCoef m θ ℓ` reads `assignUpd` first and falls back to `a0`. When the lists are consistent (Claim 1)
  and disjoint (p.9), this is the paper's `a^{(0)}` and `a`. Both are padded with zeros outside the
  listed indices, as the paper does for `a^{(0)}` at (26).
* In (22), `b` ranges over `test`, `(out, j)` for `j ∈ [m]` and `(ptr, j)` for `j ∈ [m + 1]`.
-/

/-- `B = 2^{m+5}(m + 2)`, proof of Lemma 2, p.8. -/
def Bconst (m : ℕ) : ℤ := 2 ^ (m + 5) * ((m : ℤ) + 2)

/-- The eleven assignments of (17a)–(17f) and (18) for one `j ∈ [m]`, as `(ℓ, a^{(0)}_ℓ)` pairs. -/
def assign0At (m : ℕ) (θ : ℕ → ℤ) (j : ℕ) : List (ℤ × ℤ) :=
  let P : ℤ := p m
  let pT : ℤ := piTest m
  let pR : ℤ := piRow m j
  let pO : ℤ := piOut m j
  let pP : ℤ := piPtr m j
  let pP' : ℤ := piPtr m (j + 1)
  [ (P + pT - pR, 4 * θ j),              -- (17a)
    (P + pT - pO, -(2 ^ (j + 1))),        -- (17b)
    (P + pT - pP, -(2 ^ (j + 1))),        -- (17c)
    (pO - pT, 1),                         -- (17d)
    (P + pO - pP, 1),                     -- (17e)
    (P + pP - pP', 4),                    -- (17f)
    (P + pT - pO + 1, 2 ^ (j + 1)),       -- (18)
    (P + pT - pP + 1, 2 ^ (j + 1)),       -- (18)
    (pO - pT + 1, -1),                    -- (18)
    (P + pO - pP + 1, -1),                -- (18)
    (P + pP - pP' + 1, -4) ]              -- (18)

/-- All assignments (17)–(18), for `j = 1, …, m`. -/
def assign0 (m : ℕ) (θ : ℕ → ℤ) : List (ℤ × ℤ) :=
  (List.range' 1 m).flatMap (assign0At m θ)

/-- The update assignments (22) and (23), p.9:
`a_1 = 2`, `a_{p−1} = 1 − B`, `a_p = B + 1`, `a_{p+1} = −B − 1`, `a_{π(test)} = B + 1`,
`a_{π(out,j)} = B − 2` (`j ∈ [m]`), `a_{π(ptr,j)} = B − 3` (`j ∈ [m + 1]`), `a_{π(b)+1} = B − 1`
(every `b`), and `a_ℓ = −B²` for `p/3 < ℓ ≤ 2p/3`. -/
def assignUpd (m : ℕ) : List (ℤ × ℤ) :=
  let P : ℤ := p m
  let B : ℤ := Bconst m
  [ (1, 2), (P - 1, 1 - B), (P, B + 1), (P + 1, -B - 1),
    ((piTest m : ℤ), B + 1), ((piTest m : ℤ) + 1, B - 1) ] ++
  (List.range' 1 m).flatMap (fun j => [((piOut m j : ℤ), B - 2), ((piOut m j : ℤ) + 1, B - 1)]) ++
  (List.range' 1 (m + 1)).flatMap
    (fun j => [((piPtr m j : ℤ), B - 3), ((piPtr m j : ℤ) + 1, B - 1)]) ++
  (List.range' (p m / 3 + 1) (p m / 3)).map (fun ℓ => ((ℓ : ℤ), -B ^ 2))

/-- The auxiliary coefficients `a^{(0)}_ℓ`: the value assigned to `ℓ` by (17)–(18), and `0` if `ℓ`
is not assigned. -/
def a0 (m : ℕ) (θ : ℕ → ℤ) (ℓ : ℤ) : ℤ :=
  ((assign0 m θ).lookup ℓ).getD 0

/-- The final coefficients `a_ℓ`: the value assigned by (22)–(23) if `ℓ` is updated there, and
`a^{(0)}_ℓ` otherwise. -/
def aCoef (m : ℕ) (θ : ℕ → ℤ) (ℓ : ℤ) : ℤ :=
  match (assignUpd m).lookup ℓ with
  | some v => v
  | none => a0 m θ ℓ

end AutoregLTF


