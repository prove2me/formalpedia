-- Prove2me | Definitions.Def_LocalLemmaHierarchy_Completeness_Representation
-- name    : LocalLemmaHierarchy_Completeness_Representation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:17:37.155593+00:00
-- url     : https://prove2.me/theorems/8681a7a8-e799-44df-839a-4f837f797b1f
-- title:
--   Positive local deletion representations, polynomial families, and the radii $R_U$, $R$
-- statement:
--   Sites form a set $V$ and labels a set $T$. A **positive local deletion representation** $\mathcal R$ (Definition 2.1) assigns to each site $v$ a finite set $\mathcal A(v)$ of options; each option $a$ has finite sets $v\in A_{v,a}\subseteq D_{v,a}$ (activation and deletion supports), a coefficient $c_{v,a}>0$, a label $\tau(v,a)\in T$ and a total order $\prec_{v,a}$ on $D_{v,a}\setminus\{v\}$, and $c_*:=\inf_{v,a}c_{v,a}>0$.
--
--   $\mathcal R$ **represents** the polynomial family $Z=(Z_U)_{U\Subset V}$ (finite regions $U$, polynomials in the variables $z_\tau$, $\tau\in T$) when $Z_\emptyset=1$, $Z_U(0)=1$, and for every finite $U$ and $v\in U$ the deletion identity (2.1) holds:
--   $$Z_U(z)=Z_{U-v}(z)+\sum_{a\in\mathcal A(v),\,A_{v,a}\subseteq U}c_{v,a}\,z_{\tau(v,a)}\,Z_{U\setminus D_{v,a}}(z).$$
--   The family is **nonconstant** if some $Z_U\neq 1$.
--
--   For nonnegative moduli $p=(p_\tau)$: $P_U(p)=Z_U(-p)$ and the deletion ratio $X_{U,v}(p)=1-P_U(p)/P_{U-v}(p)$ (§2.2). $Z_U$ is **zero-free on the closed polydisc** $|z_\tau|\le p_\tau$ if $Z_U(z)\ne0$ for every complex $z$ there. The **region radius** (2.2) is $R_U=\sup\{t\ge0: Z_U(z)\ne0 \text{ whenever } |z_\tau|\le t\}\in[0,\infty]$ and the **uniform radius** (2.3) is $R=R(Z)=\inf_{U\Subset V}R_U$.
--
--   **Formalization Note.** `PosLocalDeletionRep V T` bundles the option data (options at `v` form a `Fintype` `Opt v`); the order $\prec_{v,a}$ is a rank `rank v a : V → ℕ` injective on $D_{v,a}\setminus\{v\}$ ($w\prec u\iff$ rank $w<$ rank $u$); $c_*>0$ is the field `cstar_pos` (some $c_0>0$ below every coefficient), and `cstar` is the infimum itself. The family is `Z : Finset V → MvPolynomial T ℝ` (the deletion identity forces real coefficients) and `IsRepresentationOf R Z` is the identity as an equality of polynomials. Complex evaluation is `MvPolynomial.aeval`. Radii are in `ℝ≥0∞`, so $R_U=+\infty$ for $Z_U\equiv1$. Countability of $V$ is not assumed.
-- source:
--   Achlioptas, Kritharidis and Zampetakis, A Complete Hierarchy of Local Lemmas, STOC 2027 submission (manuscript sha256 bc1388b0…a434b961), Definition 2.1 and (2.1)–(2.3), printed pp. 5–6 (PDF pp. 7–8); §2.2, printed p. 6 (PDF p. 8)

import Mathlib

open scoped ENNReal NNReal

namespace LocalLemmaHierarchy.Completeness

/-- **Positive local deletion representation** (Achlioptas–Kritharidis–Zampetakis, Definition 2.1,
printed pp. 5–6 / PDF pp. 7–8), the option data only. Sites form a type `V`, labels a type `T`.
Every site `v` has a finite type of options `Opt v`; an option `a` carries an activation support
`A v a` and a deletion support `D v a` (finite, `v ∈ A v a ⊆ D v a`), a coefficient `c v a > 0`
with `c_∗ = inf c > 0`, a label `label v a ∈ T`, and a total order on `D v a \ {v}`, encoded by a
rank `rank v a : V → ℕ` that is injective on `D v a \ {v}` (`w ≺_{v,a} u ↔ rank w < rank u`).
All option data are fixed on `V`; supports need not be uniformly bounded. The polynomial family
and the deletion identity (2.1) are `IsRepresentationOf`. -/
structure PosLocalDeletionRep (V T : Type) where
  /-- the options at a site -/
  Opt : V → Type
  /-- each site has finitely many options -/
  optFintype : ∀ v, Fintype (Opt v)
  /-- activation support `A_{v,a}` -/
  A : (v : V) → Opt v → Finset V
  /-- deletion support `D_{v,a}` -/
  D : (v : V) → Opt v → Finset V
  self_mem_A : ∀ v a, v ∈ A v a
  A_subset_D : ∀ v a, A v a ⊆ D v a
  /-- coefficient `c_{v,a}` -/
  c : (v : V) → Opt v → ℝ
  c_pos : ∀ v a, 0 < c v a
  /-- `c_∗ = inf_{v,a} c_{v,a} > 0` -/
  cstar_pos : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ v a, c₀ ≤ c v a
  /-- label `τ(v,a) ∈ T` -/
  label : (v : V) → Opt v → T
  /-- the total order `≺_{v,a}` on `D_{v,a} \ {v}`, as an injective rank -/
  rank : (v : V) → Opt v → V → ℕ
  rank_injOn : ∀ v a, Set.InjOn (rank v a) ((↑(D v a) : Set V) \ {v})

attribute [instance] PosLocalDeletionRep.optFintype

variable {V T : Type}

open Classical in
/-- `R` is a positive local deletion representation of the polynomial family
`Z = (Z_U)_{U ⋐ V}` (Definition 2.1): `Z_∅ = 1`, `Z_U(0) = 1`, and for every finite region `U`
and `v ∈ U` the deletion identity (2.1)
`Z_U = Z_{U−v} + ∑_{a ∈ A(v), A_{v,a} ⊆ U} c_{v,a} z_{τ(v,a)} Z_{U \ D_{v,a}}`
holds as an identity of polynomials in the variables `z_τ`, `τ ∈ T`. -/
def IsRepresentationOf (R : PosLocalDeletionRep V T) (Z : Finset V → MvPolynomial T ℝ) : Prop :=
  Z ∅ = 1 ∧ (∀ U, MvPolynomial.eval (0 : T → ℝ) (Z U) = 1) ∧
    ∀ U : Finset V, ∀ v ∈ U,
      Z U = Z (U.erase v) +
        ∑ a ∈ Finset.univ.filter (fun a : R.Opt v => R.A v a ⊆ U),
          MvPolynomial.C (R.c v a) * MvPolynomial.X (R.label v a) * Z (U \ R.D v a)

/-- The family is **nonconstant**: some `Z_U` is not the constant polynomial `1`. -/
def IsNonconstant (Z : Finset V → MvPolynomial T ℝ) : Prop :=
  ∃ U : Finset V, Z U ≠ 1

/-- `c_∗ = inf_{v,a} c_{v,a}` (Definition 2.1). Used only for a representation with at least one
option, where the infimum is over a nonempty set bounded below by `0`. -/
noncomputable def PosLocalDeletionRep.cstar (R : PosLocalDeletionRep V T) : ℝ :=
  ⨅ p : (Σ v : V, R.Opt v), R.c p.1 p.2

/-- `P_U(p) = Z_U(−p)` (§2.2): the polynomial evaluated at the negative of the moduli `p`. -/
noncomputable def negEval (Z : Finset V → MvPolynomial T ℝ) (U : Finset V) (p : T → ℝ) : ℝ :=
  MvPolynomial.eval (fun τ => -p τ) (Z U)

/-- The deletion ratio `X_{U,v}(p) = 1 − P_U(p) / P_{U−v}(p)` (§2.2). -/
noncomputable def deletionRatio [DecidableEq V] (Z : Finset V → MvPolynomial T ℝ) (U : Finset V)
    (v : V) (p : T → ℝ) : ℝ :=
  1 - negEval Z U p / negEval Z (U.erase v) p

/-- `Z_U(z) ≠ 0` throughout the closed polydisc `|z_τ| ≤ p_τ`. -/
def ZeroFreeOn (Z : Finset V → MvPolynomial T ℝ) (U : Finset V) (p : T → ℝ) : Prop :=
  ∀ z : T → ℂ, (∀ τ, ‖z τ‖ ≤ p τ) → MvPolynomial.aeval z (Z U) ≠ 0

/-- The region radius (2.2): `R_U = sup{t ≥ 0 : Z_U(z) ≠ 0 whenever |z_τ| ≤ t}`, in `[0, ∞]`. -/
noncomputable def regionRadius (Z : Finset V → MvPolynomial T ℝ) (U : Finset V) : ℝ≥0∞ :=
  ⨆ (t : ℝ≥0) (_ : ZeroFreeOn Z U (fun _ => (t : ℝ))), (t : ℝ≥0∞)

/-- The uniform radius (2.3): `R = R(Z) = inf_{U ⋐ V} R_U`, in `[0, ∞]`. -/
noncomputable def uniformRadius (Z : Finset V → MvPolynomial T ℝ) : ℝ≥0∞ :=
  ⨅ U : Finset V, regionRadius Z U

end LocalLemmaHierarchy.Completeness


