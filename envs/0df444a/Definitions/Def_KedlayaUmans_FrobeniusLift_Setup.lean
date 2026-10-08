-- Prove2me | Definitions.Def_KedlayaUmans_FrobeniusLift_Setup
-- name    : KedlayaUmans_FrobeniusLift_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:50.124474+00:00
-- url     : https://prove2.me/theorems/9bd74744-4171-4f79-94aa-a50c9ca69299
-- title:
--   The rings 𝔽_p[W]/(P(W)) ⊆ R = 𝔽_q[W]/(P(W)), the parameter h = p^c, the Frobenius powers σ^i and E(Z) = Z^{h−1} − η (Section 6)
-- statement:
--   This file fixes the ambient objects of Section 6 of Kedlaya–Umans.
--
--   Let $p$ be a prime, let $\mathbb F_q$ be a field of characteristic $p$ (in Lean a type $F$ with `CharP F p`), and let $P(W) \in \mathbb F_p[W]$ be a polynomial of degree $c$. Define:
--
--   1. the ring $K = \mathbb F_p[W]/(P(W))$, which is a field with $p^c$ elements when $P$ is irreducible over $\mathbb F_p$;
--   2. the ring $R = \mathbb F_q[W]/(P(W))$, where the coefficients of $P$ are viewed in $\mathbb F_q$; $P$ need not remain irreducible over $\mathbb F_q$, so $R$ is in general not a field;
--   3. the integer $h = p^c$;
--   4. the embedding $\iota : K \to R$ that is the identity on $\mathbb F_p$ and sends $W$ to $W$ (the inclusion $\mathbb F_p[W]/(P(W)) \subseteq R$ of the paper);
--   5. for $i \ge 0$, the ring endomorphism $\sigma^i$ of $R$ given by $x \mapsto x^{h^i}$, where $\sigma : x \mapsto x^h$ is a power of the Frobenius endomorphism;
--   6. for $\eta \in K$, the polynomial
--   $$E(Z) = Z^{h-1} - \eta \in R[Z],$$
--   which is monic of degree $h-1 \ge 1$ when $P$ is irreducible (then $c \ge 1$).
--
--   When $P$ is irreducible over $\mathbb F_p$, the file also records that $R$ is a nontrivial ring of characteristic $p$, which is what makes $x \mapsto x^{h^i}$ a ring endomorphism, and that $E$ is monic.
--
--   These are the rings $\mathbb F_p \subseteq \mathbb F_p[W]/(P(W)) \subseteq R$ and $\mathbb F_q \subseteq R$ of Figure 2 of the paper; the ring $S = R[Z]/(E(Z))$ is built from them in the companion definition file.
--
--   **Formalization Note** The degree $c$ is not a separate parameter: it is `P.natDegree`, and $h$ is `p ^ P.natDegree`. The map $\sigma^i$ is Mathlib's `iterateFrobenius R p (c * i)`, i.e. $x \mapsto x^{p^{ci}} = x^{h^i}$. The paper's choice of $c$ as the least exponent with $p^c > m^2 d$ is imposed later, as a hypothesis of the theorems ($m^2 d < p^c$; see the theorems' notes).
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), pp. 18-19, Section 6 (construction of R, η, S = R[Z]/(E(Z)), and σ), Figure 2

import Mathlib

/-!
Kedlaya–Umans, *Fast polynomial factorization and modular composition*, Dagstuhl 08381
(version of Aug. 31, 2008), §6, pp. 18–19: the rings `K = 𝔽_p[W]/(P(W))`, `R = 𝔽_q[W]/(P(W))`,
`S = R[Z]/(E(Z))`, the parameter `h = p^c` with `c = deg P`, the embedding `K → R`, the powers of
the Frobenius `σ = (x ↦ x^h)` on `R`, and `E(Z) = Z^{h-1} - η`.
-/

open Polynomial

namespace KedlayaUmans.FrobeniusLift

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [CharP F p] (P : (ZMod p)[X])

/-- The field `𝔽_p[W]/(P(W))` (a field when `P` is irreducible over `𝔽_p`). -/
abbrev K : Type := AdjoinRoot P

/-- The ring `R = 𝔽_q[W]/(P(W))`, where `P` is viewed as a polynomial over `F = 𝔽_q`.
`P` need not stay irreducible over `F`, so `R` need not be a field. -/
abbrev R : Type _ := AdjoinRoot (P.map (ZMod.castHom (dvd_refl p) F))

/-- The parameter `h = p^c`, where `c = deg P`. -/
def h : ℕ := p ^ P.natDegree

/-- The embedding `𝔽_p[W]/(P(W)) ⊆ R`, sending `W` to `W`. -/
noncomputable def ι : K p P →+* R p F P :=
  AdjoinRoot.map (ZMod.castHom (dvd_refl p) F) P (P.map (ZMod.castHom (dvd_refl p) F)) dvd_rfl

/-- `R` is nontrivial when `P` is irreducible over `𝔽_p` (so `deg P ≥ 1`). -/
instance R.nontrivial [Fact (Irreducible P)] : Nontrivial (R p F P) :=
  AdjoinRoot.nontrivial _ (by
    rw [degree_map]
    exact (degree_pos_of_irreducible (Fact.out : Irreducible P)).ne')

/-- `R` has characteristic `p`. -/
instance R.charP [Fact (Irreducible P)] : CharP (R p F P) p :=
  charP_of_injective_algebraMap' F p

/-- `σ^i : R → R`, the `i`-th power of the Frobenius power `σ : x ↦ x^h`, i.e. `x ↦ x^{h^i}`
(`= x ↦ x^{p^{c i}}`). -/
noncomputable def sigma [Fact (Irreducible P)] (i : ℕ) : R p F P →+* R p F P :=
  iterateFrobenius (R p F P) p (P.natDegree * i)

/-- `E(Z) = Z^{h-1} - η ∈ R[Z]`, for `η ∈ 𝔽_p[W]/(P(W))` viewed in `R`. -/
noncomputable def E (η : K p P) : (R p F P)[X] :=
  X ^ (h p P - 1) - C (ι p F P η)

/-- `E` is monic, because `h - 1 ≥ 1` when `deg P ≥ 1`. -/
theorem E_monic [Fact (Irreducible P)] (η : K p P) : (E p F P η).Monic := by
  have hc : 0 < P.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible (Fact.out : Irreducible P))
  refine monic_X_pow_sub_C _ ?_
  have : 1 < p ^ P.natDegree := Nat.one_lt_pow hc.ne' (Fact.out : p.Prime).one_lt
  unfold h; omega

end KedlayaUmans.FrobeniusLift


