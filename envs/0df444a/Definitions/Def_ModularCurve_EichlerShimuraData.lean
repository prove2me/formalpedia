-- Prove2me | Definitions.Def_ModularCurve_EichlerShimuraData
-- name    : ModularCurve_EichlerShimuraData
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/e238f5ea-509e-57fc-8ece-54d742b76278
-- title:
--   Tate module, Eichler–Shimura data and λ-adic realisations
-- statement:
--   The standing setting is a field extension $L/K$, natural numbers $N$ (nonzero) and $p$, and an abelian group $J$ carrying a module structure over the abstract Hecke algebra `HeckeAlg` $=\mathbb{Z}[T_\ell : \ell \text{ prime}]$ (a polynomial ring with one variable `heckeGen ℓ` per rational prime) together with a distributive action of $L\simeq_{\mathrm{alg}K}L$ commuting with the Hecke action. [`TateModule p J`](../def/EllipticCurve_TateModule.html#L15) is the Hecke submodule of the sequence module $\mathbb{N}\to J$ consisting of those $x$ with $x_0=0$ and $p\cdot x_{n+1}=x_n$ for all $n$; thus $p^n\cdot x_n=0$ (`pow_smul_apply`), so such a sequence is a compatible system of $p^n$-torsion points, and the module is $p$-divisible in the sense that a sequence killed by some $p^k$ vanishes (`eq_zero_of_pow_smul_eq_zero`); it is stable under the group action (`smul_mem`). `FreeOfRankTwo p J` asserts the existence of $e_1,e_2$ in this Tate module such that every element $t$ satisfies $p^k\cdot t=s_1e_1+s_2e_2$ for some $k$ and some Hecke operators $s_i$, and such that any relation $s_1e_1+s_2e_2=0$ forces both $s_1$ and $s_2$ to annihilate the whole Tate module: a basis-up-to-isogeny formulation rather than freeness of a localised module. `CardinalityAJ p J g` says $\#\{x\in J: p^n x=0\}=p^{2gn}$ for all $n$. `EichlerShimuraData N p J` is a four-field proposition bundling `FreeOfRankTwo`, the condition that inertia at primes $\ell\nmid Np$ fixes all $p$-power torsion of $J$, the Frobenius relation $\sigma^2x-T_\ell(\sigma x)+\ell x=0$ on $p$-power torsion for $\sigma$ Frobenius at such $\ell$, and nonvanishing of $\mathfrak m$-torsion in $J$ for every eigenform ideal $\mathfrak m$ of level $N$ containing $p$.
--
--   `IsPPowTorsion p x` is the predicate $\exists n,\ p^nx=0$, with closure under sums, negatives, differences, the group action, Hecke operators and natural scalars. `IsLambdaAdicRealization p J k φ V π ρ` packages: $V$ a two-dimensional $k$-vector space, $\rho$ a homomorphism from $L\simeq_{\mathrm{alg}K}L$ to $\mathrm{GL}_k(V)$, and $\pi:J\to V$ sending $0$ to $0$, additive on $p$-power torsion, Galois-equivariant and $\varphi$-semilinear for the Hecke action there, with $\pi$ of the $p$-power torsion spanning $V$; consequently $\pi$ respects negation, differences and integer multiples on torsion, and an endomorphism of $V$ is determined by its values on $\pi$ of the torsion (`linearMap_eq_zero`, `linearMap_ext`). Finally `attachmentTraceData φ` is $\ell\mapsto\varphi(T_\ell)$ at primes and $0$ elsewhere, and `attachmentDetData k` is $\ell\mapsto\ell$ in $k$.
--
--   **Relation to Mathlib.** Mathlib has no Hecke algebra acting on a Jacobian and no $p$-adic Tate module of an abelian variety; `HeckeAlg` is realised as a Mathlib multivariate polynomial ring and the Tate module as a submodule of a sequence module, while torsion submodules, finrank and linear equivalences are Mathlib's.
--
--   **Where it is used.** These definitions form the interface for the Galois representation attached to a weight-two normalised eigenform on $\Gamma_0(N)$ through the $p$-adic Tate module of the Jacobian of the modular curve: `EichlerShimuraData` records the properties cited of that Tate module, and `IsLambdaAdicRealization` the two-dimensional representation extracted from it, which is what the level-lowering step and the Frey-curve argument consume.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_EichlerShimuraData.lean

import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_EigenformIdeal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section TateModule

variable (p : ℕ) {G : Type*} [Group G] (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction G J] [SMulCommClass G HeckeAlg J]

def TateModule : Submodule HeckeAlg (ℕ → J) where
  carrier := {x | x 0 = 0 ∧ ∀ n, p • x (n + 1) = x n}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨by simp [hx0, hy0], fun n => ?_⟩
    simp only [Pi.add_apply, smul_add, hx n, hy n]
  zero_mem' := ⟨rfl, fun n => smul_zero p⟩
  smul_mem' := by
    rintro s x ⟨hx0, hx⟩
    refine ⟨by simp [hx0], fun n => ?_⟩
    simp only [Pi.smul_apply]
    rw [smul_comm, hx n]

namespace TateModule

variable {p} {J}

lemma mem_iff {x : ℕ → J} :
    x ∈ TateModule p J ↔ x 0 = 0 ∧ ∀ n, p • x (n + 1) = x n :=
  Iff.rfl

lemma pow_smul_apply {x : ℕ → J} (hx : x ∈ TateModule p J) (n : ℕ) :
    p ^ n • x n = 0 := by
  induction n with
  | zero => simpa using hx.1
  | succ n ih =>
    have := hx.2 n
    calc p ^ (n + 1) • x (n + 1) = p ^ n • p • x (n + 1) := by
          rw [pow_succ, mul_smul]
      _ = p ^ n • x n := by rw [this]
      _ = 0 := ih

lemma eq_zero_of_pow_smul_eq_zero {x : ℕ → J} (hx : x ∈ TateModule p J) {k : ℕ}
    (h : p ^ k • x = 0) : x = 0 := by

  have key : ∀ m n, x n = p ^ m • x (n + m) := by
    intro m
    induction m with
    | zero => intro n; simp
    | succ m ih =>
      intro n
      calc x n = p ^ m • x (n + m) := ih n
        _ = p ^ m • (p • x (n + m + 1)) := by rw [hx.2 (n + m)]
        _ = (p ^ m * p) • x (n + m + 1) := by rw [mul_smul]
        _ = p ^ (m + 1) • x (n + (m + 1)) := by rw [← pow_succ, ← Nat.add_assoc]
  funext n
  have hk : p ^ k • x (n + k) = 0 := by
    have := congrFun h (n + k)
    simpa using this
  simp only [Pi.zero_apply]
  rw [key k n, hk]

omit [SMulCommClass G HeckeAlg J] in

lemma smul_mem (g : G) {x : ℕ → J} (hx : x ∈ TateModule p J) :
    g • x ∈ TateModule p J := by
  refine ⟨by simp [Pi.smul_apply, hx.1], fun n => ?_⟩
  simp only [Pi.smul_apply]
  rw [smul_comm, hx.2 n]

end TateModule

end TateModule

section FreeOfRankTwo

variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]

def FreeOfRankTwo : Prop :=
  ∃ e₁ e₂ : ℕ → J, e₁ ∈ TateModule p J ∧ e₂ ∈ TateModule p J ∧
    (∀ t ∈ TateModule p J, ∃ (k : ℕ) (s₁ s₂ : HeckeAlg), p ^ k • t = s₁ • e₁ + s₂ • e₂) ∧
    (∀ s₁ s₂ : HeckeAlg, s₁ • e₁ + s₂ • e₂ = 0 →
      (∀ t ∈ TateModule p J, s₁ • t = 0) ∧ (∀ t ∈ TateModule p J, s₂ • t = 0))

def CardinalityAJ (g : ℕ) : Prop :=
  ∀ n : ℕ, Nat.card {x : J // p ^ n • x = 0} = p ^ (2 * g * n)

end FreeOfRankTwo

section Bundle

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) [NeZero N] (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]

structure EichlerShimuraData : Prop where

  freeOfRankTwo : FreeOfRankTwo p J

  unramifiedOutside : UnramifiedOutside (K := K) (L := L) N p J

  frobeniusQuadratic : FrobeniusQuadratic (K := K) (L := L) N p J

  eigenformSupport : EigenformSupport p J (IsEigenformIdeal N)

end Bundle

section Torsion

variable (p : ℕ) {J : Type*} [AddCommGroup J]

def IsPPowTorsion (x : J) : Prop := ∃ n : ℕ, p ^ n • x = 0

variable {p}

lemma IsPPowTorsion.zero : IsPPowTorsion p (0 : J) := ⟨0, smul_zero _⟩

lemma IsPPowTorsion.add {x y : J} (hx : IsPPowTorsion p x) (hy : IsPPowTorsion p y) :
    IsPPowTorsion p (x + y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  refine ⟨m + n, ?_⟩
  have hx' : p ^ (m + n) • x = 0 := by rw [pow_add, mul_comm, mul_smul, hm, smul_zero]
  have hy' : p ^ (m + n) • y = 0 := by rw [pow_add, mul_smul, hn, smul_zero]
  rw [smul_add, hx', hy', add_zero]

lemma IsPPowTorsion.neg {x : J} (hx : IsPPowTorsion p x) : IsPPowTorsion p (-x) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [smul_neg, hn, neg_zero]

lemma IsPPowTorsion.sub {x y : J} (hx : IsPPowTorsion p x) (hy : IsPPowTorsion p y) :
    IsPPowTorsion p (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

private lemma nsmul_galois_smul {G : Type*} [Monoid G] [DistribMulAction G J] (σ : G)
    (m : ℕ) (x : J) : m • (σ • x) = σ • (m • x) := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]

lemma IsPPowTorsion.galois_smul {G : Type*} [Group G] [DistribMulAction G J] (σ : G)
    {x : J} (hx : IsPPowTorsion p x) : IsPPowTorsion p (σ • x) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [nsmul_galois_smul σ (p ^ n) x, hn, smul_zero]

lemma IsPPowTorsion.hecke_smul [Module HeckeAlg J] (t : HeckeAlg)
    {x : J} (hx : IsPPowTorsion p x) : IsPPowTorsion p (t • x) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul HeckeAlg (p ^ n) (t • x), ← mul_smul, mul_comm, mul_smul,
    Nat.cast_smul_eq_nsmul HeckeAlg (p ^ n) x, hn, smul_zero]

lemma IsPPowTorsion.nsmul [Module HeckeAlg J] (m : ℕ)
    {x : J} (hx : IsPPowTorsion p x) : IsPPowTorsion p (m • x) := by
  rw [← Nat.cast_smul_eq_nsmul HeckeAlg m x]
  exact hx.hecke_smul _

end Torsion

section Realization

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]
variable (k : Type*) [Field k] (φ : HeckeAlg →+* k)
variable (V : Type*) [AddCommGroup V] [Module k V]
variable (π : J → V) (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V))

structure IsLambdaAdicRealization : Prop where

  finite : Module.Finite k V

  finrank_eq : Module.finrank k V = 2

  map_zero : π 0 = 0

  map_add : ∀ x y : J, IsPPowTorsion p x → IsPPowTorsion p y → π (x + y) = π x + π y

  map_galois : ∀ (σ : L ≃ₐ[K] L) (x : J), IsPPowTorsion p x → π (σ • x) = ρ σ (π x)

  map_hecke : ∀ (t : HeckeAlg) (x : J), IsPPowTorsion p x → π (t • x) = φ t • π x

  spanning : Submodule.span k (π '' {x : J | IsPPowTorsion p x}) = ⊤

namespace IsLambdaAdicRealization

variable {p J k φ V π ρ}
variable (h : IsLambdaAdicRealization p J k φ V π ρ)
include h

lemma map_neg (x : J) (hx : IsPPowTorsion p x) : π (-x) = -π x := by
  have h0 : π (x + -x) = π x + π (-x) := h.map_add x (-x) hx hx.neg
  rw [add_neg_cancel, h.map_zero] at h0
  exact (neg_eq_of_add_eq_zero_right h0.symm).symm

lemma map_sub (x y : J) (hx : IsPPowTorsion p x) (hy : IsPPowTorsion p y) :
    π (x - y) = π x - π y := by
  rw [sub_eq_add_neg, h.map_add x (-y) hx hy.neg, h.map_neg y hy, ← sub_eq_add_neg]

lemma map_nsmul (m : ℕ) (x : J) (hx : IsPPowTorsion p x) : π (m • x) = (m : k) • π x := by
  rw [← Nat.cast_smul_eq_nsmul HeckeAlg m x, h.map_hecke _ x hx, map_natCast]

lemma linearMap_eq_zero (T : V →ₗ[k] V)
    (hT : ∀ x : J, IsPPowTorsion p x → T (π x) = 0) : T = 0 := by
  rw [← LinearMap.ker_eq_top, ← top_le_iff, ← h.spanning, Submodule.span_le]
  rintro v ⟨x, hx, rfl⟩
  exact hT x hx

lemma linearMap_ext {T₁ T₂ : V →ₗ[k] V}
    (hT : ∀ x : J, IsPPowTorsion p x → T₁ (π x) = T₂ (π x)) : T₁ = T₂ := by
  have key := h.linearMap_eq_zero (T₁ - T₂) fun x hx => by
    rw [LinearMap.sub_apply, hT x hx, sub_self]
  rwa [sub_eq_zero] at key

end IsLambdaAdicRealization

end Realization

section AttachmentData

variable {k : Type*} [Field k]

def attachmentTraceData (φ : HeckeAlg →+* k) : ℕ → k := fun ℓ =>
  if h : ℓ.Prime then φ (heckeGen ⟨ℓ, h⟩) else 0

def attachmentDetData (k : Type*) [Field k] : ℕ → k := fun ℓ => (ℓ : k)

@[simp] lemma attachmentTraceData_apply_prime (φ : HeckeAlg →+* k) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    attachmentTraceData φ ℓ = φ (heckeGen ⟨ℓ, hℓ⟩) := dif_pos hℓ

end AttachmentData

end ModularCurve


