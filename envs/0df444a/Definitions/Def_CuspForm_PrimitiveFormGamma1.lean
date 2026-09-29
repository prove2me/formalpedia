-- Prove2me | Definitions.Def_CuspForm_PrimitiveFormGamma1
-- name    : CuspForm_PrimitiveFormGamma1
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/7a57bc15-2103-596a-8419-fdd4ccedfb1a
-- title:
--   Nebentypus, normalised Hecke eigenforms, primitive forms
-- statement:
--   Fix $M \in \mathbb{N}$ and a weight $k \in \mathbb{Z}$, and for a function on the upper half-plane write $a_n =$ `qCoeff` $g\,n$ for the $n$-th coefficient of its $q$-expansion of width $1$. Four predicates on a cusp form $g$ of weight $k$ for $\Gamma_1(M)$ are defined, entirely in terms of these coefficients and of the transformation law; no Hecke operator, Petersson product or space-level structure is involved.
--
--   `HasNebentypus ε g`, for a Dirichlet character $\varepsilon$ modulo $M$ with values in $\mathbb{C}$, asserts that for every $\gamma \in SL(2,\mathbb{Z})$ lying in $\Gamma_0(M)$ and every $\tau \in \mathfrak{H}$ one has $g(\gamma\tau) = \varepsilon(d)\,(c\tau+d)^k\,g(\tau)$, where $c = \gamma_{1,0}$ and $d = \gamma_{1,1}$ are the bottom row entries, reduced mod $M$ in the argument of $\varepsilon$.
--
--   `IsEigenformWith ε g` conjoins four clauses: $a_1 = 1$; for every prime $p \nmid M$ and every $n$, $a_{pn} + \varepsilon(p)\,p^{k-1}\,[\,p \mid n\,]\,a_{n/p} = a_p a_n$; for every prime $\ell \mid M$ and every $n$, $a_{\ell n} = a_\ell a_n$; and `HasNebentypus ε g`.
--
--   `EigenpacketOccursAt k a e M'`, for functions $a, e : \mathbb{N} \to \mathbb{C}$, asserts the existence of a Dirichlet character $\varepsilon'$ modulo $M'$, a nonzero cusp form $h$ of weight $k$ for $\Gamma_1(M')$ with nebentypus $\varepsilon'$, and a finite set $S$ of naturals, such that for every prime $p \notin S$ one has $\varepsilon'(p) = e(p)$ and $c_{pn} + \varepsilon'(p)p^{k-1}[\,p\mid n\,]c_{n/p} = a(p)\,c_n$ for all $n$, where $c_n$ are the coefficients of $h$. Note that $h$ need not be normalised, and nothing is required at the primes of $S$.
--
--   `IsPrimitiveForm ε g` says that $g$ is such an eigenform and that for every divisor $M'$ of $M$ with $M' \neq M$ the packet $\bigl(a_p, \varepsilon(p)\bigr)_p$ coming from $g$ does not occur at level $M'$. Accompanying lemmas project out the individual clauses, and one records that a nonzero eigenform with $M \neq 0$ has its own packet occurring at level $M$, the exceptional set being the divisors of $M$.
--
--   **Relation to Mathlib.** Mathlib supplies `CuspForm`, the congruence subgroups $\Gamma_0(M)$, $\Gamma_1(M)$, `DirichletCharacter` and the $q$-expansion used by `qCoeff`; the notions of nebentypus, normalised Hecke eigenform and primitive form (newform) are the project's own, formulated without Hecke operators.
--
--   **Where it is used.** These notions supply the shape of the modular forms occurring on both sides of level lowering: the Frey curve yields a weight-two eigenform of some level, and primitivity at a proper divisor of the level is what the level-lowering step contradicts or produces, the Fermat deduction ending with a primitive form of weight two and level $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_PrimitiveFormGamma1.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups

namespace CuspForm

variable {M : ℕ} {k : ℤ}

def HasNebentypus (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → ∀ τ : UpperHalfPlane,
    g (γ • τ) =
      ε ((γ 1 1 : ℤ) : ZMod M) *
        ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k * g τ)

def IsEigenformWith (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) : Prop :=
  qCoeff g 1 = 1 ∧
  (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
    qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff g (n / p) else 0) =
      qCoeff g p * qCoeff g n) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ∀ n : ℕ, qCoeff g (ℓ * n) = qCoeff g ℓ * qCoeff g n) ∧
  HasNebentypus ε g

def EigenpacketOccursAt (k : ℤ) (a e : ℕ → ℂ) (M' : ℕ) : Prop :=
  ∃ (ε' : DirichletCharacter ℂ M') (h : CuspForm (Gamma1 M') k),
    h ≠ 0 ∧ HasNebentypus ε' h ∧
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ε' (p : ZMod M') = e p ∧
      ∀ n : ℕ,
        qCoeff h (p * n) +
            ε' (p : ZMod M') * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff h (n / p) else 0) =
          a p * qCoeff h n

def IsPrimitiveForm (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) : Prop :=
  IsEigenformWith ε g ∧
    ∀ M' : ℕ, M' ∣ M → M' ≠ M →
      ¬ EigenpacketOccursAt k (fun n => qCoeff g n) (fun n => ε (n : ZMod M)) M'

theorem IsEigenformWith.qCoeff_one {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) : qCoeff g 1 = 1 := h.1

theorem IsEigenformWith.hecke_of_not_dvd {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (n : ℕ) :
    qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff g (n / p) else 0) =
      qCoeff g p * qCoeff g n := h.2.1 p hp hpM n

theorem IsEigenformWith.hecke_of_dvd {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) (n : ℕ) :
    qCoeff g (ℓ * n) = qCoeff g ℓ * qCoeff g n := h.2.2.1 ℓ hℓ hℓM n

theorem IsEigenformWith.hasNebentypus {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) : HasNebentypus ε g := h.2.2.2

theorem IsPrimitiveForm.isEigenformWith {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsPrimitiveForm ε g) : IsEigenformWith ε g := h.1

theorem IsPrimitiveForm.not_eigenpacketOccursAt {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Gamma1 M) k} (h : IsPrimitiveForm ε g) {M' : ℕ} (hM' : M' ∣ M) (hne : M' ≠ M) :
    ¬ EigenpacketOccursAt k (fun n => qCoeff g n) (fun n => ε (n : ZMod M)) M' := h.2 M' hM' hne

theorem IsEigenformWith.eigenpacketOccursAt {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) (hM : M ≠ 0) (hg : g ≠ 0) :
    EigenpacketOccursAt k (fun n => qCoeff g n) (fun n => ε (n : ZMod M)) M :=
  ⟨ε, g, hg, h.hasNebentypus, Nat.divisors M, fun _ hp hpS => ⟨rfl, fun n =>
    h.hecke_of_not_dvd hp (fun hpM => hpS (Nat.mem_divisors.2 ⟨hpM, hM⟩)) n⟩⟩

end CuspForm


