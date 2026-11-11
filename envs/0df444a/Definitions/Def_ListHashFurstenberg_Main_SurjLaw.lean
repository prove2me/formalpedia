-- Prove2me | Definitions.Def_ListHashFurstenberg_Main_SurjLaw
-- name    : ListHashFurstenberg_Main_SurjLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:42.551398+00:00
-- url     : https://prove2.me/theorems/89a3ee78-c6f1-49ae-b4a2-a52109ff4675
-- title:
--   A uniformly random (surjective) linear map $f:V\to\mathbb F_q^d$ on any vector space
-- statement:
--   Let $F$ be a finite field, $V$ any vector space over $F$ (of finite or infinite dimension) and $d\ge0$. Fix a basis $(e_i)_{i\in I}$ of $V$. A linear map $f:V\to F^d$ is the same as the family of images $(f(e_i))_{i\in I}\in (F^d)^I$. A **uniformly random linear map** $V\to F^d$ is obtained by choosing the images $f(e_i)$ independently and uniformly in $F^d$; its law $\mu$ is the product of the uniform measures, which is the normalized Haar measure of the compact group $\mathrm{Hom}_F(V,F^d)\cong(F^d)^I$ and does not depend on the basis. A **uniformly random surjective linear map** is this law conditioned on surjectivity:
--
--   $$\Pr_f[P(f)]=\frac{\mu\{f:\ f\text{ surjective and }P(f)\}}{\mu\{f:\ f\text{ surjective}\}}.$$
--
--   For finite-dimensional $V$ this is the number of surjective linear maps $V\to F^d$ satisfying $P$ divided by the number of all surjective linear maps $V\to F^d$. This is the sampling model of Lemma 2.19 (an arbitrary vector space), of the proof of Theorem 2.20, and of Theorem 3.2 ($V=F^u$).
--
--   **Formalization Note** The basis is Mathlib's chosen basis `Module.Free.chooseBasis`, the product measure is `Measure.infinitePi` of uniform measures on $F^d$ (all subsets measurable), and the map is `Basis.constr`. The measure of a set that is not measurable is its outer measure; for infinite-dimensional $V$ the surjections have full measure, so the conditional law is the unconditioned one. When no surjection $V\to F^d$ exists the quotient is $0/0=0$; statements that sample a surjection assume one exists.
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, List Decoding, Linear Hashing, and Furstenberg over F_q, STOC 2027 submission #1578 (October 2026), PDF SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9, Lemma 2.19, p.19 ('uniformly random surjective linear map'); proof of Theorem 2.20, p.19; Theorem 3.2, p.20

import Mathlib

namespace ListHashFurstenberg.Main

open MeasureTheory

/-- The uniform probability measure on `F^d`, with every subset measurable. -/
noncomputable def uniformVec (F : Type*) [Fintype F] [Nonempty F] (d : ℕ) :
    @Measure (Fin d → F) ⊤ :=
  @PMF.toMeasure (Fin d → F) ⊤ (PMF.uniformOfFintype (Fin d → F))

/-- The law of a **uniformly random linear map** `V → F^d` on an arbitrary `F`-vector space `V`
(finite- or infinite-dimensional), written in the coordinates of a fixed basis `(e_i)_{i ∈ ι}` of
`V`: the images `f(e_i) ∈ F^d` are independent and uniform. This is the product of the uniform
measures, i.e. the Haar probability measure of the compact group `Hom_F(V, F^d) ≅ (F^d)^ι`. -/
noncomputable def linLaw (F : Type*) [Field F] [Fintype F] (V : Type*) [AddCommGroup V]
    [Module F V] (d : ℕ) :
    @Measure (Module.Free.ChooseBasisIndex F V → Fin d → F)
      (@MeasurableSpace.pi (Module.Free.ChooseBasisIndex F V) (fun _ => Fin d → F) fun _ => ⊤) :=
  @Measure.infinitePi (Module.Free.ChooseBasisIndex F V) (fun _ => Fin d → F) (fun _ => ⊤)
    (fun _ => uniformVec F d)

/-- The linear map `V → F^d` with prescribed images `g i` of the chosen basis vectors. -/
noncomputable def linOfCoords (F : Type*) [Field F] (V : Type*) [AddCommGroup V] [Module F V]
    (d : ℕ) (g : Module.Free.ChooseBasisIndex F V → Fin d → F) : V →ₗ[F] (Fin d → F) :=
  (Module.Free.chooseBasis F V).constr F g

/-- **Probability over a uniformly random surjective linear map** `f : V → F^d`
(Lemma 2.19, p.19, Theorem 2.20's proof, p.19, and Theorem 3.2, p.20, of Kumar–Mon, *List
Decoding, Linear Hashing, and Furstenberg over F_q*, STOC 2027 submission #1578): the uniform law
of linear maps `V → F^d` (`linLaw`) conditioned on surjectivity,
`Pr_f[P f] = μ{f surjective ∧ P f} / μ{f surjective}`.

**Formalization Note** For finite-dimensional `V` this is the number of surjective linear maps
satisfying `P` divided by the number of all surjective linear maps. For infinite-dimensional `V`
it is the Haar-measure conditional law (the surjections then have full measure). The measure of a
set is its outer measure when the set is not measurable. When no surjection `V → F^d` exists the
quotient is `0 / 0 = 0`; statements assume a surjection exists, as the source does when it samples
one. -/
noncomputable def probSurj (F : Type*) [Field F] [Fintype F] (V : Type*) [AddCommGroup V]
    [Module F V] (d : ℕ) (P : (V →ₗ[F] (Fin d → F)) → Prop) : ℝ :=
  (linLaw F V d {g | Function.Surjective (linOfCoords F V d g) ∧ P (linOfCoords F V d g)}).toReal /
    (linLaw F V d {g | Function.Surjective (linOfCoords F V d g)}).toReal

end ListHashFurstenberg.Main


