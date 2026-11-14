-- Prove2me | Definitions.Def_LatticePrepro_Tables_Construction
-- name    : LatticePrepro_Tables_Construction
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:20:49.96607+00:00
-- url     : https://prove2.me/theorems/a5e4f685-b35e-4457-afd8-ae394946710e
-- title:
--   Polynomial evaluation tables: column sums, interpolants, moment maps and constraints (Construction A.4)
-- statement:
--   Fix a prime $p$, a field setup with sample field $\mathbb{S}$ of size $q=|\mathbb{S}|$ and moment field $K=\mathbb{S}(\gamma)$ of degree $\delta$ over $\mathbb{S}$, and natural numbers $m$ (the number of axes) and $B$ (the base). An *evaluation table* is a vector $y\in\mathbb{F}_p^{\,\mathbb{S}^m\times\mathbb{S}}$. The bundle defines the objects of steps 2–5 of Construction A.4.
--
--   1. **Coordinates** (`Coord`): pairs $(\lambda,s)\in\mathbb{S}^m\times\mathbb{S}$ of a label $\lambda=(\lambda_0,\dots,\lambda_{m-1})$ and a column $s$. The $q$ columns $\{(\lambda,s):\lambda\in\mathbb{S}^m\}$ are the blocks, each of size $q^m$.
--   2. **Weighted column sums** (`colSum`): for an exponent vector $\eta\in\mathbb{N}^m$ and $s\in\mathbb{S}$,
--      $$\mathrm{colSum}(y,\eta,s)=\sum_{\lambda\in\mathbb{S}^m}y_{(\lambda,s)}\,\lambda^{\eta}\in\mathbb{S},\qquad \lambda^{\eta}=\prod_{h=0}^{m-1}\lambda_h^{\eta_h},$$
--      where $y_{(\lambda,s)}\in\mathbb{F}_p$ acts on $\mathbb{S}$ by scalar multiplication.
--   3. **Interpolants** (`interp`): $P^y_\eta\in\mathbb{S}[X]$ is the Lagrange interpolant of $s\mapsto\mathrm{colSum}(y,\eta,s)$ on all of $\mathbb{S}$, i.e. the unique polynomial of degree $<q$ with $P^y_\eta(s)=\mathrm{colSum}(y,\eta,s)$ for every $s\in\mathbb{S}$.
--   4. **Moment maps** (`mom`): $\hat\mu_k(y)=P^y_{\mathrm{digits}_{B,m}(k)}(\gamma)\in K$ for $k\in\mathbb{N}$, where $\mathrm{digits}_{B,m}$ is the generalized digit vector of Definition A.1.
--   5. **Parameters**: the index set $\mathcal{I}=\{0,\dots,2p(B-1)\}^m$ (`IdxSet`, with `IdxSet.toNat` reading an index as an exponent vector), the degree bound $\Delta=2pm(B-1)(\delta-1)$ (`degBound`), and the largest moment order $2p(B^m-1)$ (`maxOrder`), which equals $2\ell-2$ for the Hankel length $\ell=p(B^m-1)+1$.
--   6. **Constraints** (`constraintFun`): $y$ is sent to a triple in the space `ConstrW` $=\mathbb{S}^{\mathcal{I}\times\{0,\dots,q-1\}}\times K^{\mathcal{I}}\times K^{\{0,\dots,2p(B^m-1)\}}$ with components
--      - *low degree*: $(\eta,u)\mapsto$ the coefficient of $X^u$ in $P^y_\eta$ if $u>\Delta$, and $0$ otherwise;
--      - *index consistency*: $\eta\mapsto P^y_\eta(\gamma)-\hat\mu_{\mathrm{val}_B(\eta)}(y)$;
--      - *Frobenius*: $k\mapsto\hat\mu_{pk}(y)-\hat\mu_k(y)^p$ if $pk\le2p(B^m-1)$, and $0$ otherwise.
--
--      The table satisfies the paper's evaluation table constraints $T\cdot y=0$ exactly when $\mathrm{constraintFun}(y)=0$.
--
--   These are the evaluation tables, moment maps and constraint system of the explicit moment representation. Together with the element tables of step 6 they form the moment representation of Theorem A.8.
--
--   **Formalization Note**: The constraints are a map into a product of spaces rather than a matrix over $\mathbb{F}_p$. Expanding each component in fixed $\mathbb{F}_p$-bases gives the paper's matrix $T$, and the source module shows that `constraintFun` and `mom` are $\mathbb{F}_p$-linear. Low-degree rows are indexed by all $u<q$ (`Fin (Fintype.card 𝕊)`), and the rows with $u\le\Delta$ are $0$. `mom` is defined for every $k\in\mathbb{N}$, though only orders $k\le2p(B^m-1)$ are used. The definitions take an arbitrary field setup and arbitrary $m,B$; the paper's choices of $\delta$ and $q$ enter only in Theorem A.8. The paper writes $\mathbb{K},\mathbb{E},\tau,c,\zeta,\mathsf a,\mathsf d,W_{\deg},\nu$ for $\mathbb{S},K,q,\delta,\gamma,m,B,\Delta,\ell$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Construction A.4 (\label{con:moment-representation}), steps 2–5; Lean: LatticePrepro/Tables/Construction.lean, LatticePrepro.ExplicitTables.{Coord, colSum, interp, mom, IdxSet, IdxSet.toNat, degBound, maxOrder, ConstrW, constraintFun}

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup

/-!
# Polynomial evaluation tables: the construction (Construction A.4)

Fix a field setup `FS` (sample field `𝕊` of size `q`, moment field `K = 𝕊(γ)` of degree `δ`)
and integers `m ≥ 1`, `B ≥ 2`. An evaluation table is a vector `y : (Fin m → 𝕊) × 𝕊 → 𝔽_p`;
its coordinates `(λ, s)` are partitioned into the `q` columns `s ∈ 𝕊`, each of size `q^m`.

* `colSum y η s = ∑ λ, y (λ, s) • λ^η` is the weighted column sum for the exponent vector `η`.
* `interp y η ∈ 𝕊[X]` is the polynomial of degree `< q` interpolating `s ↦ colSum y η s`.
* `mom y k = (interp y (gdigits B m k)) (γ)` is the `k`-th moment map.
* `constraintFun y` collects the low-degree, index-consistency and Frobenius constraints.

All of these are `𝔽_p`-linear in `y`.
-/

namespace LatticePrepro

open Polynomial

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

/-- Coordinates of an evaluation table: a label `λ ∈ 𝕊^m` and a column `s ∈ 𝕊`. -/
abbrev Coord : Type := (Fin m → FS.𝕊) × FS.𝕊

/-- The weighted column sum `∑ λ, y (λ, s) • λ^η`. -/
def colSum (y : Coord FS m → ZMod p) (η : Fin m → ℕ) (s : FS.𝕊) : FS.𝕊 :=
  ∑ lam : Fin m → FS.𝕊, y (lam, s) • ∏ h, lam h ^ η h

/-- The interpolating polynomial of the column sums (degree `< q`). -/
noncomputable def interp (y : Coord FS m → ZMod p) (η : Fin m → ℕ) : FS.𝕊[X] :=
  Lagrange.interpolate (Finset.univ : Finset FS.𝕊) id (fun s => colSum FS m y η s)

/-- The `k`-th moment map `M̂_k(y) = P^y_{digits(k)}(γ)`. -/
noncomputable def mom (y : Coord FS m → ZMod p) (k : ℕ) : FS.K :=
  aeval FS.γ (interp FS m y (gdigits B m k))

/-! ### Parameters -/

/-- The exponent index set `I = {0, …, 2p(B-1)}^m`. -/
abbrev IdxSet (p m B : ℕ) : Type := Fin m → Fin (2 * p * (B - 1) + 1)

/-- An index as an exponent vector. -/
def IdxSet.toNat {p m B : ℕ} (η : IdxSet p m B) : Fin m → ℕ := fun h => (η h).val

/-- The degree bound `Δ = 2 p m (B - 1) (δ - 1)`. -/
def degBound (p m B δ : ℕ) : ℕ := 2 * p * m * (B - 1) * (δ - 1)

/-- The largest moment order carried by a table, `2ℓ - 2 = 2 p (B^m - 1)` where
`ℓ = p (B^m - 1) + 1` is the Hankel length. -/
def maxOrder (p m B : ℕ) : ℕ := 2 * p * (B ^ m - 1)

/-- The codomain of the constraint map: low-degree rows, index-consistency rows and
Frobenius rows. -/
abbrev ConstrW : Type :=
  (IdxSet p m B × Fin (Fintype.card FS.𝕊) → FS.𝕊) × (IdxSet p m B → FS.K) ×
    (Fin (maxOrder p m B + 1) → FS.K)

/-- The evaluation table constraints (Construction A.4, step 5), as a function of `y`. -/
noncomputable def constraintFun (y : Coord FS m → ZMod p) : ConstrW FS m B :=
  (fun ηu => if degBound p m B δ < ηu.2.val then (interp FS m y ηu.1.toNat).coeff ηu.2.val else 0,
   fun η => aeval FS.γ (interp FS m y η.toNat) - mom FS m B y (digitVal B η.toNat),
   fun k => if p * k.val ≤ maxOrder p m B then
     mom FS m B y (p * k.val) - (mom FS m B y k.val) ^ p else 0)

/-! ### Unpacking the constraints -/

end ExplicitTables

end LatticePrepro


