-- Prove2me | Definitions.Def_CuspForm_ModPForms
-- name    : CuspForm_ModPForms
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/c15093c4-94e4-56c1-a5d3-989865fddc6f
-- title:
--   Mod-p forms: reduced q-expansions, theta and Hecke operators
-- statement:
--   Fix a field $F$, a level $N$ and a weight $k \in \mathbb{Z}$. [`ModPForms.modPCusp N k F`](../def/CuspForm_ModPForms.html#L7) is the $F$-submodule of the formal power series ring $F[[q]]$ spanned by the following set: those $\varphi$ for which there are a cusp form $f$ of weight $k$ on $\Gamma_0(N)$ and a sequence $a \colon \mathbb{N} \to \mathbb{Z}$ with $\mathrm{qCoeff}\, f\, n = a_n$ in $\mathbb{C}$ for all $n$ (here $\mathrm{qCoeff}\, f\, n$ is the $n$-th coefficient of the $q$-expansion of $f$ of width $1$, i.e. in $q = e^{2\pi i \tau}$), and $\varphi = \sum_n \bar a_n q^n$ with $\bar a_n$ the image of $a_n$ in $F$. Thus the generators are exactly the coefficientwise reductions to $F$ of those cusp forms whose $q$-expansion is integral, and the span is taken inside $F[[q]]$. [`ModPForms.modPMod N k F`](../def/CuspForm_ModPForms.html#L12) is defined in the same way with `ModularForm` in place of `CuspForm`, so that Eisenstein contributions are allowed.
--
--   Two operators on $F[[q]]$ are defined purely coefficientwise. [`ModPForms.thetaPS`](../def/CuspForm_ModPForms.html#L17) sends $\varphi$ to the series with $n$-th coefficient $n \cdot a_n(\varphi)$, i.e. $\theta = q\,d/dq$. [`ModPForms.heckePS k ℓ`](../def/CuspForm_ModPForms.html#L20) sends $\varphi$ to the series whose $n$-th coefficient is $a_{n\ell}(\varphi) + \ell^{k-1} a_{n/\ell}(\varphi)$ when $\ell \mid n$, and $a_{n\ell}(\varphi)$ otherwise, the factor $\ell^{k-1}$ being the integer power of the image of $\ell$ in $F$; it is defined for every natural number $\ell$, primality not being imposed.
--
--   Finally [`ModPForms.IsModPEigen N S₀ k φ lam`](../def/CuspForm_ModPForms.html#L24), for a set $S_0$ of naturals and a function $\mathrm{lam} \colon \mathbb{N} \to F$, asserts that $\varphi \neq 0$ and that $\mathrm{heckePS}\ k\ \ell\ \varphi = \mathrm{lam}(\ell) \cdot \varphi$ for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S_0$. It is a condition on an arbitrary power series: membership in `modPCusp` or `modPMod` is not part of it, the eigenvalue function is unconstrained away from such $\ell$, and enlarging $S_0$ weakens the requirement.
--
--   **Relation to Mathlib.** Mathlib supplies `ModularForm`, `CuspForm`, `CongruenceSubgroup.Gamma0` and the $q$-expansion used through the project's [`ModularFormClass.qCoeff`](../def/FLTPrelim_Modularity.html#L19), but has no notion of mod-$p$ modular forms, nor of the theta operator or Hecke operators acting on formal $q$-expansions; all five declarations here are the project's own.
--
--   **Where it is used.** These definitions give a coefficient-level, characteristic-$p$ substitute for spaces of modular forms and their Hecke action, in which congruences between $q$-expansions and systems of mod-$p$ Hecke eigenvalues can be stated without constructing mod-$p$ modular curves; such systems are the data transported in the level-lowering step of the Frey–Serre–Ribet argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_ModPForms.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModPForms

def modPCusp (N : ℕ) (k : ℤ) (F : Type) [Field F] : Submodule F (PowerSeries F) :=
  Submodule.span F
    {φ | ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (a : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : F)}

def modPMod (N : ℕ) (k : ℤ) (F : Type) [Field F] : Submodule F (PowerSeries F) :=
  Submodule.span F
    {φ | ∃ (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (a : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) ∧ φ = PowerSeries.mk fun n => ((a n : ℤ) : F)}

noncomputable def thetaPS {F : Type} [Field F] (φ : PowerSeries F) : PowerSeries F :=
  PowerSeries.mk fun n => (n : F) * PowerSeries.coeff n φ

noncomputable def heckePS {F : Type} [Field F] (k : ℤ) (ℓ : ℕ) (φ : PowerSeries F) : PowerSeries F :=
  PowerSeries.mk fun n =>
    PowerSeries.coeff (n * ℓ) φ + if ℓ ∣ n then (ℓ : F) ^ (k - 1) * PowerSeries.coeff (n / ℓ) φ else 0

def IsModPEigen {F : Type} [Field F] (N : ℕ) (S₀ : Set ℕ) (k : ℤ) (φ : PowerSeries F) (lam : ℕ → F) : Prop :=
  φ ≠ 0 ∧
    ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → heckePS k ℓ φ = lam ℓ • φ

end ModPForms


