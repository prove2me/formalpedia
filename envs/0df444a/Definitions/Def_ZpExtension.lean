-- Prove2me | Definitions.Def_ZpExtension
-- name    : ZpExtension
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T02:39:47.56831+00:00
-- url     : https://prove2.me/theorems/a5ea2a56-6625-41e2-bfcd-26b4fc346edf
-- title:
--   $\mathbb{Z}_p$-extension of a field
-- statement:
--   Let $p$ be a prime number and let $L/K$ be a (possibly infinite) algebraic extension of fields. Following Iwasawa, $L/K$ is called a **$\mathbb{Z}_p$-extension** if
--
--   1. $L/K$ is Galois (normal and separable), and
--   2. the Galois group $\Gamma = \mathrm{Gal}(L/K)$, equipped with its Krull (profinite) topology, is isomorphic **as a topological group** to the additive group of $p$-adic integers:
--   $$
--   \mathrm{Gal}(L/K) \;\cong\; \mathbb{Z}_p .
--   $$
--
--   This is the basic object of Iwasawa theory. For a number field $K$ and an odd prime $p$, the cyclotomic $\mathbb{Z}_p$-extension (the unique subfield of $K(\mu_{p^\infty})$ with Galois group $\mathbb{Z}_p$ over $K$) is the prototypical example; for a CM field one also has the anticyclotomic and other $\mathbb{Z}_p$-extensions, and Leopoldt's conjecture for $K$ is equivalent to $K$ having exactly $r_2+1$ independent $\mathbb{Z}_p$-extensions. The finite layers $K_n$ of a $\mathbb{Z}_p$-extension, with $\mathrm{Gal}(K_n/K)\cong \mathbb{Z}/p^n\mathbb{Z}$, are the fields to which Iwasawa's growth formula for class numbers applies.
--
--   **Formalization Note** The Galois group is Mathlib's `L ≃ₐ[K] L` (notation `Gal(L/K)`) with the Krull topology instance `krullTopology`. Galois-ness is Mathlib's `IsGalois K L`, which makes sense for infinite extensions. The additive group $\mathbb{Z}_p$ is written multiplicatively as `Multiplicative ℤ_[p]`, and the isomorphism is a `ContinuousMulEquiv` (`≃ₜ*`), i.e. a group isomorphism that is a homeomorphism. The predicate only asserts the existence of such an isomorphism (no choice of topological generator).
-- source:
--   L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Springer 1997, §13.1: 'a Γ-extension ... Galois extension K_∞/K with Gal(K_∞/K) ≅ Γ ≅ ℤ_p'; K. Iwasawa, On Γ-extensions of algebraic number fields, Bull. AMS 65 (1959) 183–226.

import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# `ℤ_p`-extensions

Following Iwasawa (see Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §13.1),
a `ℤ_p`-extension of a field `K` is a Galois extension `L / K` (possibly infinite) whose Galois
group `Gal(L/K)`, with its Krull topology, is topologically isomorphic to the additive group
of `p`-adic integers `ℤ_p`.

* `IsZpExtension p K L`: `L / K` is Galois and `Gal(L/K) ≃ₜ* Multiplicative ℤ_[p]`.
-/

/-- `L / K` is a `ℤ_p`-extension: `L / K` is a (possibly infinite) Galois extension and its
Galois group `Gal(L/K) = L ≃ₐ[K] L`, equipped with the Krull topology, is isomorphic as a
topological group to the additive group `ℤ_p` (written multiplicatively). -/
def IsZpExtension (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Prop :=
  IsGalois K L ∧ Nonempty (Gal(L/K) ≃ₜ* Multiplicative ℤ_[p])


