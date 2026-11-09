-- Prove2me | Definitions.Def_RSListDecodingCapacity_AllRates_LocalRank
-- name    : RSListDecodingCapacity_AllRates_LocalRank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:38.178851+00:00
-- url     : https://prove2.me/theorems/64e459b1-fc07-409d-8224-dccefb381860
-- title:
--   The space $V$, the index set $I$, the rewriting (22) and the map $\Gamma:V\to\mathbb F^I$
-- statement:
--   Fix $d\ge1$, $m$ and $W$. Work in $\mathbb F[T,U,Y_1,\dots,Y_d]$ and $\mathbb F[T,E,Y_1,\dots,Y_d]$; for a monomial write $c=(c_2,\dots,c_d)$ for the exponents of $Y_2,\dots,Y_d$.
--
--   1. $V=\mathrm{span}\{T^rU^aY_1^bY^c:0\le r<m,\ 0\le a\le r,\ 0\le b\le m,\ \omega(c)\le W+r\}$, a subspace of $\mathbb F[T,U,Y_1,\dots,Y_d]/(T^m)$, represented by its monomials of $T$-degree below $m$.
--   2. $I=\{(i,b,e_1,c):i+db<m,\ e_1\le 2m-1,\ \omega(c)\le W+m-1\}$, the exponent vectors of monomials $T^iE^bY_1^{e_1}Y^c$ required to vanish by (16).
--   3. Rewriting (22): $E=U-\sum_{j=1}^d(-1)^{j+1}T^{j-1}Y_j$, i.e. substitute $U=E+\sum_{j=1}^d(-1)^{j+1}T^{j-1}Y_j$.
--   4. $\Gamma:V\to\mathbb F^I$ sends $F$ to the family of coefficients of $T^iE^bY_1^{e_1}Y^c$, $(i,b,e_1,c)\in I$, of $F$ rewritten in the variables $T,E,Y$.
--   5. The element $E=U-\sum_{j=1}^d(-1)^{j+1}T^{j-1}Y_j$ itself, and $h_r=\lceil (m-r)/d\rceil$ for $0\le r<m$.
--
--   The rank of $\Gamma$ bounds the number of independent local constraints contributed by one received point.
--
--   **Formalization Note** Coefficients with $i<m$ do not depend on the representative of $F$ modulo $T^m$, so $\Gamma$ is computed on the canonical representative. Variables are the types `UVar d` and `LVar d`, with `Y j` the source's $Y_{j+1}$.
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), §3.2.2, pp.21–22, including (22) and h_r

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Parameters
import Definitions.Def_RSListDecodingCapacity_AllRates_LocalConstraints

namespace RSListDecodingCapacity.AllRates

/-!
# The rank bound of §3.2.2: the space `V`, the index set `I` and the map `Γ`

Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565, §3.2.2, pp.21–22, including (22),
and the definition of `h_r` on p.22.
-/

/-- The variables `T, U, Y₁, …, Y_d` of the intermediate substitution `Y₀ = y + T U` (p.21–22);
`Y j` (`j : Fin d`) is the source's `Y_{j+1}`. -/
inductive UVar (d : ℕ) where
  | T : UVar d
  | U : UVar d
  | Y : Fin d → UVar d

/-- The exponent of `Y₁` in a monomial of `𝔽[T, U, Y₁, …, Y_d]` (`0` when `d = 0`). -/
def y1U {d : ℕ} (s : UVar d →₀ ℕ) : ℕ := if h : 0 < d then s (UVar.Y ⟨0, h⟩) else 0

/-- The exponent vector `c = (c₂, …, c_d)` of `Y₂, …, Y_d` in a monomial of `𝔽[T, U, Y]`
(Lean index `i` is `c_{i+2}`). -/
def cOfU {d : ℕ} (s : UVar d →₀ ℕ) : Fin (d - 1) → ℕ :=
  fun i => s (UVar.Y ⟨(i : ℕ) + 1, by omega⟩)

/-- The exponent of `Y₁` in a monomial of `𝔽[T, E, Y₁, …, Y_d]` (`0` when `d = 0`). -/
def y1L {d : ℕ} (s : LVar d →₀ ℕ) : ℕ := if h : 0 < d then s (LVar.Y ⟨0, h⟩) else 0

/-- The exponent vector `c = (c₂, …, c_d)` of `Y₂, …, Y_d` in a monomial of `𝔽[T, E, Y]`. -/
def cOfL {d : ℕ} (s : LVar d →₀ ℕ) : Fin (d - 1) → ℕ :=
  fun i => s (LVar.Y ⟨(i : ℕ) + 1, by omega⟩)

/-- **The space `V`** (p.22):
`V = span{T^r U^a Y₁^b Y^c : 0 ≤ r < m, 0 ≤ a ≤ r, 0 ≤ b ≤ m, ω(c) ≤ W + r}`. Its monomials have
`T`-degree below `m`, so `V` is the same as its image in `𝔽[T, U, Y₁, …, Y_d]/(T^m)`; these
monomials are the canonical representatives of that quotient. -/
noncomputable def Vspace (F : Type*) [CommRing F] (d m W : ℕ) :
    Submodule F (MvPolynomial (UVar d) F) :=
  MvPolynomial.restrictSupport F {s | s UVar.T < m ∧ s UVar.U ≤ s UVar.T ∧ y1U s ≤ m ∧
    omegaW (cOfU s) ≤ W + s UVar.T}

/-- **The index set `I`** (p.21): exponent vectors `(i, b, e₁, c)` of monomials
`T^i E^b Y₁^{e₁} Y^c` with `i + d b < m`, `e₁ ≤ 2m − 1` and `ω(c) ≤ W + m − 1`. The exponents of
`Y₂, …, Y_d` form `c`. -/
def IndexI (d m W : ℕ) : Type :=
  {s : LVar d →₀ ℕ // s LVar.T + d * s LVar.E < m ∧ y1L s ≤ 2 * m - 1 ∧
    omegaW (cOfL s) ≤ W + m - 1}

/-- **The rewriting (22)** (p.22): a polynomial in `T, U, Y₁, …, Y_d` is rewritten in the variables
`T, E, Y₁, …, Y_d` using `E = U − ∑_{j=1}^{d} (−1)^{j+1} T^{j−1} Y_j`, i.e. by substituting
`U = E + ∑_{j=1}^{d} (−1)^{j+1} T^{j−1} Y_j`. The Lean index `i : Fin d` stands for `j = i + 1`. -/
noncomputable def rewriteE (F : Type*) [CommRing F] (d : ℕ) :
    MvPolynomial (UVar d) F →ₐ[F] MvPolynomial (LVar d) F :=
  MvPolynomial.aeval fun v => match v with
    | UVar.T => MvPolynomial.X LVar.T
    | UVar.U => MvPolynomial.X LVar.E + ∑ i : Fin d, (-1 : MvPolynomial (LVar d) F) ^ ((i : ℕ) + 2) *
        MvPolynomial.X LVar.T ^ (i : ℕ) * MvPolynomial.X (LVar.Y i)
    | UVar.Y i => MvPolynomial.X (LVar.Y i)

/-- **The map `Γ : V → 𝔽^I`** (p.22): for `F ∈ V` and `(i, b, e₁, c) ∈ I`, `Γ(F)_{(i,b,e₁,c)}` is
the coefficient of `T^i E^b Y₁^{e₁} Y^c` after rewriting `F` in the variables `T, E, Y` by (22).
(Coefficients with `i < m` do not depend on the representative of `F` modulo `T^m`.) -/
noncomputable def Gamma (F : Type*) [CommRing F] (d m W : ℕ) :
    Vspace F d m W →ₗ[F] (IndexI d m W → F) :=
  LinearMap.pi fun s : IndexI d m W =>
    (MvPolynomial.lcoeff F s.1).comp ((rewriteE F d).toLinearMap.comp (Vspace F d m W).subtype)

/-- The element `E = U − ∑_{j=1}^{d} (−1)^{j+1} T^{j−1} Y_j` of `𝔽[T, U, Y₁, …, Y_d]` ((22),
p.22). -/
noncomputable def Eelt (F : Type*) [CommRing F] (d : ℕ) : MvPolynomial (UVar d) F :=
  MvPolynomial.X UVar.U - ∑ i : Fin d, (-1 : MvPolynomial (UVar d) F) ^ ((i : ℕ) + 2) *
    MvPolynomial.X UVar.T ^ (i : ℕ) * MvPolynomial.X (UVar.Y i)

/-- `h_r = ⌈(m − r)/d⌉` (p.22), as an integer. -/
noncomputable def hr (d m r : ℕ) : ℤ := ⌈((m : ℝ) - r) / d⌉

end RSListDecodingCapacity.AllRates


