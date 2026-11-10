-- Prove2me | Definitions.Def_HoneycombCodes_pDir
-- name    : HoneycombCodes_pDir
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:39.369075+00:00
-- url     : https://prove2.me/theorems/bcb2042a-aeb4-4987-8ebb-c1dffed24478
-- title:
--   Two-row box-transfer weights $p^\pm_{\sigma\tau}$, valid triples, $D_\omega$, $d_k$ and $J_\Omega$
-- statement:
--   Fix $n$ and $0\le k\le n/2$. A triple $\omega=(i,j,\ell)$ is **valid** if the partitions $\lambda=(n-i-j,j)$ and $\mu=(i-\ell,\ell)$ exist and, with $A_0=n-i-2j$, $B_0=i-2\ell$, $E_0=n-2k$, the triangle condition $|A_0-B_0|\le E_0\le A_0+B_0$ holds. The two-row Specht dimension is $f_{(m-r,r)}=\binom mr-\binom m{r-1}$ ($\binom m{-1}=0$).
--
--   For a forward edge of type $(\sigma,\tau)\in\{0,1\}^2$ from $\omega$ to $\omega'=(i+1,j-\sigma,\ell+\tau)$, with spins $a_\sigma=\frac{n-i-1}{2}-(j-\sigma)$, $d=\frac i2-\ell$, $e=\frac n2-k$ and
--
--   $$
--   Q(a,d,e)=\frac{(e+\frac12)^2-(a-d)^2}{(2a+1)(2d+1)},\qquad R^2_{\sigma\sigma}=Q(a_\sigma,d,e),\quad R^2_{\sigma,1-\sigma}=1-Q(a_\sigma,d,e),
--   $$
--
--   the squared contraction coefficients are
--
--   $$
--   p^+_{\sigma\tau}=\frac{n-i}{n}\,\frac{f_{\lambda'}}{f_\lambda}\,R^2_{\sigma\tau},\qquad p^-_{\sigma\tau}=\frac{i+1}{n}\,\frac{f_\mu}{f_{\mu'}}\,R^2_{\sigma\tau},
--   $$
--
--   set to $0$ unless both endpoints are valid. The directed weights are $p_{\omega,\omega'}=p^+_{\sigma\tau}(\omega)$ and $p_{\omega',\omega}=p^-_{\sigma\tau}(\omega)$, all other pairs having weight $0$. Further $D_\omega=\binom ni f_{(n-i-j,j)}f_{(i-\ell,\ell)}$, $d_k=f_{(n-k,k)}$, $(J_\Omega)_{\omega,\omega'}=\sqrt{p_{\omega,\omega'}p_{\omega',\omega}}$, and $\Omega$ is **connected** if the graph with edges $(J_\Omega)_{\omega,\omega'}>0$ is connected.
--
--   **Formalization Note** Triples are `ℕ × ℕ × ℕ`; spins and Specht dimensions are real, so no natural-number truncation occurs. The Racah factor is the closed form (35) of Remark 4.7, not a Wigner 6j symbol (Remark 4.7 and App. A.2 identify the two).
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), Proposition 4.1 and §4.2, pp.17–18 (PDF 19–20); eq. (26), p.18; Theorem 4.4, eqs. (32)–(34), p.22 (PDF 24); Remark 4.7, eq. (35), p.23 (PDF 25); eqs. (36)–(37), p.24 (PDF 26)

import Mathlib

set_option autoImplicit false

namespace HoneycombCodes

/-- The two-row **Specht dimension** `f_{(m−r, r)} = C(m, r) − C(m, r − 1)`, with `C(m, −1) = 0`,
Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2
(sha256 f4b07e31…cd51), eqs. (36), (42), pp.24–25 (PDF 26–27).

**Formalization Note.** Real-valued, so that no natural-number truncation occurs; `r = 0` gives
`C(m, 0) = 1`. It is the dimension of `S^{(m−r, r)}` when `2r ≤ m`, the only case used. -/
noncomputable def specht2 (m r : ℕ) : ℝ :=
  (m.choose r : ℝ) - (if r = 0 then 0 else (m.choose (r - 1) : ℝ))

/-- A triple `ω = (i, j, ℓ)` is **valid** at `(n, k)` when the partitions `λ = (n − i − j, j)`
and `µ = (i − ℓ, ℓ)` exist and the triangle condition (25) `|A₀ − B₀| ≤ E₀ ≤ A₀ + B₀` holds, with
`A₀ = n − i − 2j`, `B₀ = i − 2ℓ`, `E₀ = n − 2k` (24), arXiv:2608.20287v2, Proposition 4.1 and the
paragraph after it, p.17 (PDF 19).

**Formalization Note.** Triples are `ℕ × ℕ × ℕ` with `ω.1 = i`, `ω.2.1 = j`, `ω.2.2 = ℓ`; the
partition conditions are `i ≤ n`, `2j ≤ n − i`, `2ℓ ≤ i`; (25) is checked in `ℤ`. -/
def IsValidTriple (n k : ℕ) (ω : ℕ × ℕ × ℕ) : Prop :=
  ω.1 ≤ n ∧ 2 * ω.2.1 ≤ n - ω.1 ∧ 2 * ω.2.2 ≤ ω.1 ∧
    |((n : ℤ) - ω.1 - 2 * ω.2.1) - ((ω.1 : ℤ) - 2 * ω.2.2)| ≤ (n : ℤ) - 2 * k ∧
    (n : ℤ) - 2 * k ≤ ((n : ℤ) - ω.1 - 2 * ω.2.1) + ((ω.1 : ℤ) - 2 * ω.2.2)

/-- The forward box-transfer target `(i + 1, j − σ, ℓ + τ)` of type `(σ, τ)`,
arXiv:2608.20287v2, §4.2, p.18 (PDF 20). Used only when `σ ≤ j`. -/
def target (ω : ℕ × ℕ × ℕ) (σ τ : Fin 2) : ℕ × ℕ × ℕ :=
  (ω.1 + 1, ω.2.1 - σ.val, ω.2.2 + τ.val)

/-- The half-spin closed form (35) = (117),
`Q(a, d, e) = ((e + 1/2)² − (a − d)²)/((2a + 1)(2d + 1))`, arXiv:2608.20287v2, Remark 4.7,
p.23 (PDF 25), and App. A.2, p.53 (PDF 55). -/
noncomputable def Qrac (a d e : ℝ) : ℝ :=
  ((e + 1 / 2) ^ 2 - (a - d) ^ 2) / ((2 * a + 1) * (2 * d + 1))

/-- The squared Racah factor of the edge of type `(σ, τ)` leaving `ω = (i, j, ℓ)` at `(n, k)`:
`R²_{σσ} = Q_σ` and `R²_{σ,1−σ} = 1 − Q_σ`, where `Q_σ = Q(a_σ, d, e)` with the spins (26)
`a_σ = (n − i − 1)/2 − (j − σ)`, `d = i/2 − ℓ`, `e = n/2 − k`, arXiv:2608.20287v2, (26), p.18,
and Remark 4.7, p.23 (PDF 25).

**Formalization Note.** Spins are computed in `ℝ`. The weights are given by this closed form, not
by a Wigner 6j symbol (paper.md decision 7). -/
noncomputable def R2coef (n k : ℕ) (σ τ : Fin 2) (ω : ℕ × ℕ × ℕ) : ℝ :=
  let a : ℝ := ((n : ℝ) - ω.1 - 1) / 2 - ((ω.2.1 : ℝ) - σ.val)
  let d : ℝ := (ω.1 : ℝ) / 2 - ω.2.2
  let e : ℝ := (n : ℝ) / 2 - k
  if σ = τ then Qrac a d e else 1 - Qrac a d e

open Classical in
/-- The squared **forward contraction coefficient** (32),
`p⁺_{στ}(i, j, ℓ; k) = ((n − i)/n)(f_{λ′}/f_λ) R²_{στ}` with `λ = (n − i − j, j)` and
`λ′ = (n − i − 1 − (j − σ), j − σ)`, arXiv:2608.20287v2, Theorem 4.4, p.22 (PDF 24).

**Formalization Note.** Set to `0` unless `σ ≤ j` and both the source and the target triple are
valid ("we set p± = 0 whenever λ′ or µ′ is not a partition … or the target triple violates the
triangle inequality", Remark 4.7, p.23). -/
noncomputable def pPlus (n k : ℕ) (σ τ : Fin 2) (ω : ℕ × ℕ × ℕ) : ℝ :=
  if σ.val ≤ ω.2.1 ∧ IsValidTriple n k ω ∧ IsValidTriple n k (target ω σ τ) then
    ((n : ℝ) - ω.1) / n * (specht2 (n - ω.1 - 1) (ω.2.1 - σ.val) / specht2 (n - ω.1) ω.2.1) *
      R2coef n k σ τ ω
  else 0

open Classical in
/-- The squared **reverse contraction coefficient** (33),
`p⁻_{στ}(i, j, ℓ; k) = ((i + 1)/n)(f_µ/f_{µ′}) R²_{στ}` with `µ = (i − ℓ, ℓ)` and
`µ′ = (i + 1 − (ℓ + τ), ℓ + τ)`, arXiv:2608.20287v2, Theorem 4.4, p.22 (PDF 24); same zero
convention as `pPlus`. -/
noncomputable def pMinus (n k : ℕ) (σ τ : Fin 2) (ω : ℕ × ℕ × ℕ) : ℝ :=
  if σ.val ≤ ω.2.1 ∧ IsValidTriple n k ω ∧ IsValidTriple n k (target ω σ τ) then
    ((ω.1 : ℝ) + 1) / n * (specht2 ω.1 ω.2.2 / specht2 (ω.1 + 1) (ω.2.2 + τ.val)) *
      R2coef n k σ τ ω
  else 0

open Classical in
/-- The **directed box-transfer weight** `p_{ω,ω′}` at `(n, k)`: for `ν = (i + 1, j − σ, ℓ + τ)`
one has `p_{ω,ν} = p⁺_{στ}(ω; k)` and `p_{ν,ω} = p⁻_{στ}(ω; k)`; every other pair has weight `0`,
arXiv:2608.20287v2, §4.2–4.4, pp.18–24 (PDF 20–26). -/
noncomputable def pDir (n k : ℕ) (ω ω' : ℕ × ℕ × ℕ) : ℝ :=
  ∑ σ : Fin 2, ∑ τ : Fin 2,
    ((if σ.val ≤ ω.2.1 ∧ ω' = target ω σ τ then pPlus n k σ τ ω else 0) +
      (if σ.val ≤ ω'.2.1 ∧ ω = target ω' σ τ then pMinus n k σ τ ω' else 0))

/-- The ambient dimension `D_ω = C(n, i) f_{(n−i−j, j)} f_{(i−ℓ, ℓ)}` (37), arXiv:2608.20287v2,
p.24 (PDF 26). -/
noncomputable def Domega (n : ℕ) (ω : ℕ × ℕ × ℕ) : ℝ :=
  (n.choose ω.1 : ℝ) * specht2 (n - ω.1) ω.2.1 * specht2 ω.1 ω.2.2

/-- The moving stabilizer rank `d_k = f_{(n−k, k)} = C(n, k) − C(n, k − 1)` (36),
arXiv:2608.20287v2, p.24 (PDF 26). -/
noncomputable def dk (n k : ℕ) : ℝ :=
  specht2 n k

/-- The matrix `(J_Ω)_{ω,ω′} = √(p_{ω,ω′} p_{ω′,ω})` on a finite set `Ω` of triples,
arXiv:2608.20287v2, §4.4, p.23 (PDF 25). -/
noncomputable def JOmega (n k : ℕ) (Ω : Finset (ℕ × ℕ × ℕ)) : Matrix Ω Ω ℝ :=
  fun ω ω' => Real.sqrt (pDir n k ω ω' * pDir n k ω' ω)

/-- `Ω` is **connected in the positive-weight box-transfer graph**: the graph on `Ω` with an edge
`ω ∼ ω′` whenever `ω ≠ ω′` and `(J_Ω)_{ω,ω′} > 0` is connected (in particular `Ω ≠ ∅`),
arXiv:2608.20287v2, §4.4, p.23 (PDF 25). -/
def IsConnectedOmega (n k : ℕ) (Ω : Finset (ℕ × ℕ × ℕ)) : Prop :=
  (SimpleGraph.fromRel (fun ω ω' : Ω => 0 < JOmega n k Ω ω ω')).Connected

end HoneycombCodes


