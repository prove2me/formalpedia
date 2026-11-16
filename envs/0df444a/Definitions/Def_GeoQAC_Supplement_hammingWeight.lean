-- Prove2me | Definitions.Def_GeoQAC_Supplement_hammingWeight
-- name    : GeoQAC_Supplement_hammingWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:16:13.133127+00:00
-- url     : https://prove2.me/theorems/4be39a58-5775-4dd2-ab77-34109a11710f
-- title:
--   Hamming weight, $\mathrm{MAJ}_n$ and $\mathrm{MOD}_{r,n}$
-- statement:
--   For a bit string $x\in\{0,1\}^n$, the **Hamming weight** $|x|$ is the number of coordinates equal to $1$. The **majority** and **modular counting** functions are
--   $$
--   \mathrm{MAJ}_n(x)=\mathbf 1\{|x|>n/2\},\qquad \mathrm{MOD}_{r,n}(x)=\mathbf 1\{|x|\equiv 0 \pmod r\}.
--   $$
--   The paper uses $\mathrm{MOD}_{r,n}$ for a fixed modulus $r\ge 2$.
--
--   These are the symmetric functions, besides PARITY, whose width and depth requirements the paper determines in 2D-QAC and 1D-QAC.
--
--   **Formalization Note** Boolean functions are maps $(\mathrm{Fin}\,n\to\mathrm{Bool})\to\mathrm{Bool}$, like the published `GeoQAC.parityFn`. $|x|>n/2$ is written $n<2|x|$ in $\mathbb N$, which is the same condition. `modFn r n` is defined for every $r$; every statement using it assumes $r\ge2$.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), §2.1, p.9 (Hamming weight); §3.5, p.26 (MOD); p.27 (MAJ)

import Mathlib

namespace GeoQAC.Supplement

/-!
# Hamming weight, `MAJ_n` and `MOD_{r,n}`

Dong, Ou, Yao, *On the Computational Power of Geometrically Local QAC circuits*, arXiv:2604.07178
(version of 2026-11-03), §2.1, p.9 ("`|x|` denotes the Hamming weight of a bit string `x`"), §3.5,
p.26 ("For a fixed modulus `r ≥ 2`, let `MOD_{r,n}(x) = 1{|x| ≡ 0 (mod r)}`") and p.27 ("We define
`MAJ_n(x) = 1{|x| > n/2}`").

**Formalization Note.** A Boolean function is `(Fin n → Bool) → Bool`, like the published
`GeoQAC.parityFn`. `|x| > n/2` is written `n < 2·|x|` in `ℕ`, which is the same condition without
division. `modFn r n` is defined for every `r`; the paper uses it for `r ≥ 2`, and every statement
that uses it assumes this.
-/

/-- The Hamming weight `|x|`: the number of coordinates of `x` equal to `1` (p.9). -/
def hammingWeight {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun j => x j = true).card

/-- `MAJ_n(x) = 1{|x| > n/2}` (p.27). -/
def majFn (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide (n < 2 * hammingWeight x)

/-- `MOD_{r,n}(x) = 1{|x| ≡ 0 (mod r)}` (p.26). -/
def modFn (r n : ℕ) (x : Fin n → Bool) : Bool :=
  decide (hammingWeight x % r = 0)

end GeoQAC.Supplement


