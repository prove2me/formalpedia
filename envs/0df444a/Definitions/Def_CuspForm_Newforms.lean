-- Prove2me | Definitions.Def_CuspForm_Newforms
-- name    : CuspForm_Newforms
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/d4d28058-7c49-5c7d-a8a9-c56bcaefb680
-- title:
--   Eigensystem-level newforms and congruence enlargement for the Frey curve
-- statement:
--   For a weight-$2$ cusp form $f$ on $\Gamma_0(N)$ the module defines [`CuspForm.GoodEigensystemOccursAt f M`](../def/CuspForm_Newforms.html#L15): there is a normalised eigenform $g$ of weight $2$ on $\Gamma_0(M)$ whose $q$-expansion coefficients agree with those of $f$ at every prime $\ell \nmid N$ (note the exclusion set is governed by the level $N$ of $f$, and $M$ is not required to divide $N$). Then [`CuspForm.IsNewform f`](../def/CuspForm_Newforms.html#L23) asserts that $f$ is a normalised eigenform and that its good-prime eigensystem occurs at no proper divisor level, i.e. `GoodEigensystemOccursAt f M` fails for every $M \mid N$ with $M \neq N$; this is newness at the level of eigensystems (primitivity), not via the Petersson orthogonal complement of the oldforms. The per-prime variant [`CuspForm.IsNewformAt q f`](../def/CuspForm_Newforms.html#L32) asks only that $f$ be a normalised eigenform, that $q \mid N$, and that the eigensystem not occur at level $N/q$ (natural-number division). Helper lemmas record that the eigensystem of a normalised eigenform occurs at its own level, that a newform is a nonzero normalised eigenform, and that for prime $q \mid N$ with $N \neq 0$ newness implies newness at $q$. The predicate [`CuspForm.NewformBadPrimeCoeff N`](../def/CuspForm_Newforms.html#L42) is a named hypothesis, not a theorem: for every newform $f$ on $\Gamma_0(N)$ and every prime $q \mid N$, $a_q(f)^2 = 1$ if $q \| N$ and $a_q(f) = 0$ if $q^2 \mid N$.
--
--   On the arithmetic side, [`FreyPackage.ModularRepOfNewLevelLE P N M`](../def/CuspForm_Newforms.html#L56) asserts the existence of a newform $f$ of weight $2$ on $\Gamma_0(M)$, an integral Weierstrass model $W$ of the Frey curve of $P$, and a maximal ideal $\mathfrak m$ of the ring of algebraic integers `integralClosure ℤ ℂ` containing $P.p$, such that for every prime $\ell$ of good reduction for $W$ with $\ell \nmid N$ and $\ell \neq P.p$ there is an algebraic integer $a$ equal to $a_\ell(f)$ in $\mathbb C$ with $a \equiv a_\ell(W) \pmod{\mathfrak m}$ — a congruence of traces on a chosen integral model, not an isomorphism of Galois representations. [`FreyPackage.CongruenceEnlargement P`](../def/CuspForm_Newforms.html#L65) is the statement that, whenever $M \mid N$, $M > 0$, and the mod-$P.p$ representation of the Frey curve is irreducible (over `AlgebraicClosure ℚ`), a witness for `ModularRepOfNewLevelLE P N M` can be improved to one for `ModularRepOfNewLevelLE P M M`, i.e. the set of primes carrying the congruence is enlarged from $\ell \nmid N$ to $\ell \nmid M$. A local `DecidableEq` instance on `AlgebraicClosure ℚ` is provided by classical choice. The predicates `IsNormalizedEigenform`, `IsIntegralModelOf`, `IsGoodPrimeFor`, `apOfModel` and `GaloisRepIsIrreducible` come from the imported definition modules.
--
--   **Relation to Mathlib.** Mathlib supplies the underlying objects — `CuspForm`, `CongruenceSubgroup.Gamma0`, the $q$-expansion coefficients [`ModularFormClass.qCoeff`](../def/FLTPrelim_Modularity.html#L19), and `integralClosure ℤ ℂ` — but no theory of newforms; the newness predicates here are the project's own, formulated at the level of good-prime eigensystems rather than through Hecke-module decompositions.
--
--   **Where it is used.** These predicates form the interface between modularity of the Frey curve and level lowering: a modular eigensystem congruent to the Frey curve's mod-$p$ representation is first replaced by a newform of smaller level by eigensystem descent, the congruence set is then enlarged by `CongruenceEnlargement`, and `NewformBadPrimeCoeff` converts eigensystem-level newness into the statements about $a_q$ at bad primes that the level-lowering results consume.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_Newforms.lean

import Definitions.Def_FreyPackage_LevelRaising
import Definitions.Def_FLTPrelim_GaloisRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine.Point
open ModularFormClass

namespace CuspForm

variable {N : ℕ}

def GoodEigensystemOccursAt (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (M : ℕ) : Prop :=
  ∃ g : CuspForm (CongruenceSubgroup.Gamma0 M) 2, g.IsNormalizedEigenform ∧
    ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → qCoeff g ℓ = qCoeff f ℓ

lemma GoodEigensystemOccursAt.refl {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : f.IsNormalizedEigenform) : GoodEigensystemOccursAt f N :=
  ⟨f, hf, fun _ _ _ => rfl⟩

def IsNewform (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : Prop :=
  f.IsNormalizedEigenform ∧ ∀ M : ℕ, M ∣ N → M ≠ N → ¬ GoodEigensystemOccursAt f M

lemma IsNewform.isNormalizedEigenform {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform) :
    f.IsNormalizedEigenform := hf.1

lemma IsNewform.ne_zero {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform) : f ≠ 0 :=
  hf.1.ne_zero

def IsNewformAt (q : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : Prop :=
  f.IsNormalizedEigenform ∧ q ∣ N ∧ ¬ GoodEigensystemOccursAt f (N / q)

lemma IsNewform.isNewformAt {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform)
    {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) (hN : N ≠ 0) : f.IsNewformAt q :=
  ⟨hf.1, hqN, hf.2 (N / q) (Nat.div_dvd_of_dvd hqN)
    (Nat.div_lt_self (Nat.pos_of_ne_zero hN) hq.one_lt).ne⟩

variable (N) in

def NewformBadPrimeCoeff : Prop :=
  ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2), f.IsNewform →
    ∀ q : ℕ, q.Prime → q ∣ N →
      (¬ q ^ 2 ∣ N → qCoeff f q ^ 2 = 1) ∧ (q ^ 2 ∣ N → qCoeff f q = 0)

end CuspForm

namespace FreyPackage

open CuspForm

noncomputable local instance instDecEqQbarNewforms :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def ModularRepOfNewLevelLE (P : FreyPackage) (N M : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (W : WeierstrassCurve ℤ)
      (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNewform ∧ W.IsIntegralModelOf P.freyCurve ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

def CongruenceEnlargement (P : FreyPackage) : Prop :=
  ∀ N M : ℕ, M ∣ N → 0 < M →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.ModularRepOfNewLevelLE N M → P.ModularRepOfNewLevelLE M M

end FreyPackage

end


