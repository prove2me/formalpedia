-- Prove2me | Definitions.Def_CharPSComp_J
-- name    : CharPSComp_J
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:18.119899+00:00
-- url     : https://prove2.me/theorems/a06826db-ef0a-4677-808a-f72bcce435a1
-- title:
--   Truncation, strided outer polynomials, $\Phi_k$, $N$, $K$, $\gamma_w$, the node answers $J_{w,t}$ and the level-merge formula
-- statement:
--   The objects of the Frobenius recursion (§3.1–3.2, §3.6.1). Throughout, $R$ is a commutative ring and $F\in R[x]$.
--
--   1. **Truncation** $F \bmod x^u\triangleq\sum_{i=0}^{u-1}([x^i]F)\,x^i$ (`trunc u F`), and $\mathrm{polyOf}(a,\ell)=\sum_{i<\ell}a_ix^i$ for a coefficient array $a$.
--   2. **Strided outer polynomial**: for a stride $w\ge1$ and $0\le t<w$, $f_{w,t}(y)\triangleq\sum_{i\ge0,\ t+wi<m}f_{t+wi}\,y^i$.
--   3. **$\Phi_k$** raises every coefficient to the $k$-th power: $\Phi_k\big(\sum_i a_iy^i\big)=\sum_i a_i^k y^i$. It is a function on $R[y]$ for any commutative ring, a ring map only in characteristic $p$.
--   4. $N\triangleq p^{\lceil\log_pn\rceil}$ and $K\triangleq p^{\lceil\log_p\sigma\rceil}$ with $\sigma=\min(m,n)$, the least powers of $p$ that are at least $n$, resp. $\sigma$.
--   5. For a power $w$ of $p$ dividing $N$ and $u=N/w$: $\gamma_w(z)\triangleq\Phi_w(g)(z)\bmod z^u$ and the **node answer** $J_{w,t}(x)\triangleq f_{w,t}(\gamma_w(x))\bmod x^u$.
--   6. **Level merge** (§3.2): from powers $G_r$ the $k\times k$ left matrix $A_{j,r}(z)\triangleq\sum_{i<v}([x^{ki+j}]G_r)z^i$; from child answers $H_{r,t}$ (child $t+wr$) the matrix $C\triangleq AH\bmod z^v$ entrywise, and the recombined parent $\sum_{j<k}x^jC_{j,t}(x^k)$.
--   7. **Prime-power characteristic** (§3.6.1): $u_j\triangleq N/p^j$, $h_j(x)\triangleq(\gamma_{p^j}(x))^\eta\bmod x^{u_j}$ and the tree-$\alpha$ node answer $J^{(\alpha)}_{w,t}(x)\triangleq f_{\eta w,\alpha+\eta t}(h_j(x))\bmod x^{u_j}$ at $w=p^j$.
--
--   At the root $f_{1,0}=f$ and $\gamma_1=g\bmod x^N$, so $J_{1,0}=f(g(x))\bmod x^N$.
--
--   **Formalization Note** $f_{w,t}$ sums over $i<m$ with the guard $t+wi<m$, which is the page's sum for $w\ge1$; for $t\ge m$ it is $0$. $\Phi_k$ sums up to `natDegree`, which is the page's value for $k\ge1$. $N,K$ use `Nat.clog`.
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), §2.1, p.4 (PDF p.5); §3 preamble and §3.1, pp.5–6 (PDF pp.6–7); §3.2, p.7 (PDF p.8); §3.6.1, p.15 (PDF p.16)

import Mathlib

namespace CharPSComp

open Polynomial

variable {R : Type*} [CommRing R]

/-- Truncation to precision `u` (Zhu, *Faster Power Series Composition in Fixed Positive
Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), §2.1, p.4, PDF p.5):
`F(x) mod xᵘ ≜ Σ_{i=0}^{u−1} ([xⁱ]F(x)) xⁱ`. -/
noncomputable def trunc (u : ℕ) (F : R[X]) : R[X] :=
  ∑ i ∈ Finset.range u, C (F.coeff i) * X ^ i

/-- The polynomial `Σ_{i<len} a(i) xⁱ` with coefficient array `a`. -/
noncomputable def polyOf (a : ℕ → R) (len : ℕ) : R[X] :=
  ∑ i ∈ Finset.range len, C (a i) * X ^ i

/-- The strided outer polynomial (ibid., §3.1, p.5, PDF p.6):
`f_{w,t}(y) ≜ Σ_{i ≥ 0, t + wi < m} f_{t+wi} yⁱ`.

**Formalization Note** The paper uses a positive stride `w`; for `w ≥ 1` every index `i` with
`t + wi < m` is below `m`, so the sum over `i < m` is the paper's sum. -/
noncomputable def strided (f : R[X]) (m w t : ℕ) : R[X] :=
  ∑ i ∈ Finset.range m, if t + w * i < m then C (f.coeff (t + w * i)) * X ^ i else 0

/-- `Φ_k` raises every coefficient to the `k`-th power (ibid., §3.1, p.6, PDF p.7):
`Φ_k(A)(y) ≜ Σ_{i=0}^{ℓ−1} a_i^k yⁱ` for `A(y) = Σ_{i=0}^{ℓ−1} a_i yⁱ`.

**Formalization Note** The paper uses `k = pʲ ≥ 1`; then `0^k = 0`, so summing up to
`natDegree A` gives the paper's value for every representation length `ℓ`. It is a plain function
on `R[X]` over any commutative ring (a ring map only in characteristic `p`). -/
noncomputable def Phi (k : ℕ) (A : R[X]) : R[X] :=
  ∑ i ∈ Finset.range (A.natDegree + 1), C (A.coeff i ^ k) * X ^ i

/-- `N ≜ p^{⌈log_p n⌉}`, the least power of `p` that is at least `n` (ibid., §3, p.5, PDF p.6). -/
def Npow (p n : ℕ) : ℕ := p ^ Nat.clog p n

/-- `K ≜ p^{⌈log_p σ⌉}` with `σ = min(m, n)` (ibid., §3, p.5, PDF p.6). -/
def Kpow (p m n : ℕ) : ℕ := p ^ Nat.clog p (min m n)

/-- `γ_w(z) ≜ Φ_w(g)(z) mod zᵘ` with `u = N/w` (ibid., §3.1, p.6, PDF p.7). -/
noncomputable def gamma (N w : ℕ) (g : R[X]) : R[X] := trunc (N / w) (Phi w g)

/-- The node answer `J_{w,t}(x) ≜ f_{w,t}(γ_w(x)) mod xᵘ` with `u = N/w` (ibid., §3.1, p.6,
PDF p.7). The arguments are `N`, the outer length bound `m`, the width `w` and the index `t`. -/
noncomputable def J (N m w t : ℕ) (f g : R[X]) : R[X] :=
  trunc (N / w) ((strided f m w t).comp (gamma N w g))

/-- Entry `(j, r)` of the left matrix (ibid., §3.2, p.7, PDF p.8):
`A_{j,r}(z) ≜ Σ_{i=0}^{v−1} ([x^{ki+j}] G_r(x)) zⁱ`, built from the powers `G_r`. -/
noncomputable def leftMat (k v : ℕ) (G : ℕ → R[X]) (j r : ℕ) : R[X] :=
  ∑ i ∈ Finset.range v, C ((G r).coeff (k * i + j)) * X ^ i

/-- Entry `(j, t)` of `C(z) ≜ A(z) H(z) mod zᵛ` (ibid., (2), p.7, PDF p.8), where `A` is the
`k × k` left matrix of the powers `G` and `H` is the `k × w` matrix with entries
`H_{r,t} = Hc(t + wr)` (the child answers at width `wk`, index `t + wr`). -/
noncomputable def mergeMat (k v w : ℕ) (G Hc : ℕ → R[X]) (j t : ℕ) : R[X] :=
  trunc v (∑ r ∈ Finset.range k, leftMat k v G j r * Hc (t + w * r))

/-- The recombined parent answer `Σ_{j=0}^{k−1} xʲ C_{j,t}(xᵏ)` (ibid., (2), p.7, PDF p.8). -/
noncomputable def mergeOut (k v w : ℕ) (G Hc : ℕ → R[X]) (t : ℕ) : R[X] :=
  ∑ j ∈ Finset.range k, X ^ j * expand R k (mergeMat k v w G Hc j t)

/-- Prime-power characteristic (ibid., §3.6.1, p.15, PDF p.16): `u_j ≜ N/pʲ` and
`h_j(x) ≜ (γ_{pʲ}(x))^η mod x^{u_j}`. -/
noncomputable def hpow (N p η j : ℕ) (g : R[X]) : R[X] :=
  trunc (N / p ^ j) ((gamma N (p ^ j) g) ^ η)

/-- Node `t` of tree `α` at width `w = pʲ` in prime-power characteristic (ibid., §3.6.1, p.15,
PDF p.16): `J^{(α)}_{w,t}(x) ≜ f_{ηw, α+ηt}(h_j(x)) mod x^{u_j}`. -/
noncomputable def Jpe (N m p η j α t : ℕ) (f g : R[X]) : R[X] :=
  trunc (N / p ^ j) ((strided f m (η * p ^ j) (α + η * t)).comp (hpow N p η j g))

end CharPSComp


