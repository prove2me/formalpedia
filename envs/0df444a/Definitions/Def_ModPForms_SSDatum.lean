-- Prove2me | Definitions.Def_ModPForms_SSDatum
-- name    : ModPForms_SSDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/865ff995-218d-5bff-a506-32c4f794a0c2
-- title:
--   Axiomatised supersingular datum for mod-p modular forms
-- statement:
--   Fix a natural number $p$, a level $N'$, a set $S_0 \subseteq \mathbb{N}$ of excluded primes and a field $F$ of characteristic $p$. The structure [`ModPForms.SSDatum p N' S₀ F`](../def/ModPForms_SSDatum.html#L7) packages, as data and as propositional fields, the formal properties of a graded family of Hecke modules attached to the supersingular locus. Its data are: an $F$-vector space $S\,k$ for every integer $k$, together with an $F$-linear endomorphism $T\,k\,\ell$ of $S\,k$ for every natural number $\ell$; for each $k \ge p+2$ an $F$-linear map $\mathrm{res}\,k$ from the submodule $\mathrm{modPMod}\,N'\,k\,F$ of $F[[q]]$ — the $F$-span of the power series $\sum_n \bar a_n q^n$ arising from weight-$k$ modular forms on $\Gamma_0(N')$ whose $q$-expansion coefficients are integers $a_n$ — into $S\,k$; and for each $k \ge 1$ an $F$-linear isomorphism $\mathrm{bIso}\,k : S\,k \xrightarrow{\sim} S(k+p+1)$.
--
--   The propositional fields assert, for all primes $\ell \nmid N'$ with $\ell \notin S_0$: stability of $\mathrm{modPMod}\,N'\,k\,F$ under the formal Hecke operator $\mathrm{heckePS}\,k\,\ell$, whose $n$-th coefficient is $c_{n\ell}(\varphi) + [\ell \mid n]\,\ell^{k-1} c_{n/\ell}(\varphi)$, for $k \ge p+2$; equivariance of $\mathrm{res}\,k$ for $\mathrm{heckePS}\,k\,\ell$ and $T\,k\,\ell$; that any $\varphi \in \mathrm{modPMod}\,N'\,k\,F$ with $\mathrm{res}\,k\,\varphi = 0$ lies in $\mathrm{modPMod}\,N'\,(k-(p-1))\,F$; that $T(k+p+1)\,\ell \circ \mathrm{bIso}\,k = \ell \cdot (\mathrm{bIso}\,k \circ T\,k\,\ell)$ for $k \ge 1$; and a pullback property: for $1 \le k' \le p+1$, any nonzero $v \in S\,k'$ with $T\,k'\,\ell\,v = \mu_\ell v$ for all such $\ell$ admits a weight $2 \le k'' \le p+1$, an exponent $j \in \mathbb{N}$ and a $\psi \in \mathrm{modPMod}\,N'\,k''\,F$ which is a mod-$p$ eigenform in the sense of `IsModPEigen` (nonzero, with $\mathrm{heckePS}\,k''\,\ell\,\psi = \nu_\ell \psi$) with eigenvalues $\nu_\ell = \ell^{j}\mu_\ell$.
--
--   **Relation to Mathlib.** Mathlib has modular and cusp forms for congruence subgroups and their $q$-expansions, but no mod-$p$ reduction of $q$-expansions, no formal Hecke operator on power series and no notion of supersingular Hecke module; `modPMod`, `heckePS`, `IsModPEigen` and this structure are the project's own.
--
--   **Where it is used.** A datum of this shape is the input to the weight-window (theta-cycle) argument, which from it concludes that the Hecke eigensystem of a mod-$p$ eigenform of large filtration is realised, after twisting by a power of $\ell$, in some weight between $2$ and $p+1$. That weight optimisation belongs to the Serre-conjecture side of the level-lowering step for the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModPForms_SSDatum.lean

import Definitions.Def_CuspForm_ModPForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModPForms

structure SSDatum (p : ℕ) (N' : ℕ) (S₀ : Set ℕ) (F : Type) [Field F] [CharP F p] where

  S : ℤ → Type
  addCommGroup : ∀ k, AddCommGroup (S k)
  module : ∀ k, Module F (S k)

  T : ∀ (k : ℤ) (_ : ℕ), letI := addCommGroup k; letI := module k; S k →ₗ[F] S k

  hecke_stable : ∀ (k : ℤ), (p : ℤ) + 2 ≤ k → ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ →
    ∀ φ ∈ modPMod N' k F, heckePS k ℓ φ ∈ modPMod N' k F

  res : ∀ k : ℤ, (p : ℤ) + 2 ≤ k → letI := addCommGroup k; letI := module k;
    ↥(modPMod N' k F) →ₗ[F] S k

  res_equivariant : ∀ (k : ℤ) (hk : (p : ℤ) + 2 ≤ k) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N') (hℓS : ℓ ∉ S₀)
    (φ : PowerSeries F) (hφ : φ ∈ modPMod N' k F),
    letI := addCommGroup k; letI := module k;
    res k hk ⟨heckePS k ℓ φ, hecke_stable k hk ℓ hℓ hℓN hℓS φ hφ⟩ = T k ℓ (res k hk ⟨φ, hφ⟩)

  res_ker : ∀ (k : ℤ) (hk : (p : ℤ) + 2 ≤ k) (φ : PowerSeries F) (hφ : φ ∈ modPMod N' k F),
    letI := addCommGroup k; letI := module k;
    res k hk ⟨φ, hφ⟩ = 0 → φ ∈ modPMod N' (k - ((p : ℤ) - 1)) F

  bIso : ∀ k : ℤ, 1 ≤ k → letI := addCommGroup k; letI := module k;
    letI := addCommGroup (k + ((p : ℤ) + 1)); letI := module (k + ((p : ℤ) + 1));
    S k ≃ₗ[F] S (k + ((p : ℤ) + 1))
  bIso_equivariant : ∀ (k : ℤ) (hk : 1 ≤ k) (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ →
    ∀ v : S k,
    letI := addCommGroup k; letI := module k;
    letI := addCommGroup (k + ((p : ℤ) + 1)); letI := module (k + ((p : ℤ) + 1));
    T (k + ((p : ℤ) + 1)) ℓ (bIso k hk v) = (ℓ : F) • bIso k hk (T k ℓ v)

  pullback : ∀ (k' : ℤ), 1 ≤ k' → k' ≤ (p : ℤ) + 1 →
    ∀ (v : S k') (mu : ℕ → F),
    letI := addCommGroup k'; letI := module k';
    v ≠ 0 → (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ → T k' ℓ v = mu ℓ • v) →
    ∃ k'' : ℤ, 2 ≤ k'' ∧ k'' ≤ (p : ℤ) + 1 ∧ ∃ (j : ℕ) (ψ : PowerSeries F) (nu : ℕ → F),
      ψ ∈ modPMod N' k'' F ∧ IsModPEigen N' S₀ k'' ψ nu ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ → nu ℓ = (ℓ : F) ^ j * mu ℓ

end ModPForms


