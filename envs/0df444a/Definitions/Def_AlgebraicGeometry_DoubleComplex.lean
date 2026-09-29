-- Prove2me | Definitions.Def_AlgebraicGeometry_DoubleComplex
-- name    : AlgebraicGeometry_DoubleComplex
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/0a8f375f-d48d-5451-9a9b-8a7d2155d697
-- title:
--   Bounded double complexes: total complex and weak convergence
-- statement:
--   For a commutative ring $R$, [`DoubleComplex.Bounded R`](../def/AlgebraicGeometry_DoubleComplex.html#L11) is a hand-built structure packaging a first-quadrant double complex of $R$-modules: modules $C^{p,q}$ for $p,q\in\mathbb N$ (with their additive and module structures as fields), $R$-linear maps $d_H\colon C^{p,q}\to C^{p+1,q}$ and $d_V\colon C^{p,q}\to C^{p,q+1}$, the relations $d_H\circ d_H=0$, $d_V\circ d_V=0$ and the commuting (not anticommuting) square $d_V\circ d_H=d_H\circ d_V$, together with a bound $N$ and the requirement that $C^{p,q}$ be a subsingleton (hence zero) whenever $N\le p$ or $N\le q$. On such a $D$, `Diag n` is the set of pairs with $p+q=n$, `Tot D n` the product $\prod_{p+q=n}C^{p,q}$, and `dTot` the map whose component at $(p,q)$ is $d_H$ applied to the $(p-1,q)$ entry plus $(-1)^p\,d_V$ applied to the $(p,q-1)$ entry (the missing terms being $0$ at the edges); the helper lemmas `dTot_apply_zero_succ`, `dTot_apply_succ_zero`, `dTot_apply_succ_succ` record these components and `dTot_comp_dTot` proves $d^{n+1}\circ d^n=0$. `HTot D n` is $\ker d^{\,n}$ modulo the submodule `HTotB D n`, which is $\bot$ for $n=0$ and the preimage of $\operatorname{im} d^{\,n-1}$ otherwise. Columnwise, `colH D p q` is $\ker d_V$ modulo the image of the previous $d_V$ (again $\bot$ in degree $0$), `colHdH` the map induced by $d_H$, and `E₂I D p q` the quotient of $\ker(\mathrm{colHdH})$ by the preimage of the image of the preceding `colHdH`, i.e. ${}'E_2^{p,q}=H^p_h H^q_v$; `transpose` swaps the two indices and differentials, and `E₂II D p q` is `E₂I (transpose D) q p`.
--
--   `SubQuot R M` is a pair of submodules $B\le Z$ of $M$, with carrier $Z/B$. `Convergence R E₂ H N` is a structure recording, for families $E_2^{p,q}$ and $H^n$ of $R$-modules, a deliberately partial convergence statement as data: subquotients $E_\infty^{p,q}\subseteq E_2^{p,q}$ with $Z_\infty^{p,0}=\top$; for each $p$ a monotone filtration indexed by `Fin (N+1)` of $E_2^{p,0}$ from $\bot$ to $B_\infty^{p,0}$ each of whose graded pieces admits a linear isomorphism onto the carrier of some subquotient of some $E_2^{p',q'}$ with $q'\ge 1$; and for each $n$ a monotone filtration indexed by `Fin (N+2)` of $H^n$ from $\bot$ to $\top$ such that, for $p\le N$, the $p$-th graded piece of the filtration of $H^p$ is isomorphic to $E_\infty^{p,0}$. Nothing is asserted about the other graded pieces of $H^n$. `BoundedSpectralSequence` is the proposition that every bounded double complex over every commutative ring admits such convergence data for $({}'E_2, H^\bullet(\mathrm{Tot}), N)$.
--
--   **Relation to Mathlib.** These are the project's own notions: the double complex, its total complex and the two spectral-sequence pages are set up directly on $\mathbb N$-indexed families of modules with explicit kernels and quotients, rather than through Mathlib's `HomologicalComplex` machinery, and `Convergence` axiomatises the convergence conclusion as a structure.
--
--   **Where it is used.** The convergence data are used to transfer finiteness from the abutment $H^\bullet(\mathrm{Tot}\,C)$ and from the rows $q\ge 1$ to the bottom row $q=0$, which is how Serre–Grothendieck finiteness of coherent cohomology on projective schemes is obtained in this development; the module is imported throughout the algebraic-geometry layer of the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_DoubleComplex.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace DoubleComplex

structure Bounded (R : Type u) [CommRing R] where

  C : ℕ → ℕ → Type u
  [abGrp : ∀ p q, AddCommGroup (C p q)]
  [modR : ∀ p q, Module R (C p q)]

  dH : ∀ p q, C p q →ₗ[R] C (p + 1) q

  dV : ∀ p q, C p q →ₗ[R] C p (q + 1)
  dH_sq : ∀ p q, dH (p + 1) q ∘ₗ dH p q = 0
  dV_sq : ∀ p q, dV p (q + 1) ∘ₗ dV p q = 0

  dHV_comm : ∀ p q, dV (p + 1) q ∘ₗ dH p q = dH p (q + 1) ∘ₗ dV p q

  N : ℕ
  hBound : ∀ p q, N ≤ p ∨ N ≤ q → Subsingleton (C p q)

attribute [instance] Bounded.abGrp Bounded.modR

section Tot

variable {R : Type u} [CommRing R] (D : Bounded R)

abbrev Diag (n : ℕ) : Type := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

abbrev Tot (n : ℕ) : Type u :=
  ∀ i : Diag n, D.C i.1.1 i.1.2

def dTotH {n : ℕ} (i : Diag (n + 1)) :
    Tot D n →ₗ[R] D.C i.1.1 i.1.2 :=
  match i with
  | ⟨(0, _), _⟩ => 0
  | ⟨(p' + 1, q), h⟩ => (D.dH p' q).comp
      (LinearMap.proj (R := R)
        (φ := fun j : Diag n => D.C j.1.1 j.1.2) ⟨(p', q), by omega⟩)

def dTotV {n : ℕ} (i : Diag (n + 1)) :
    Tot D n →ₗ[R] D.C i.1.1 i.1.2 :=
  match i with
  | ⟨(_, 0), _⟩ => 0
  | ⟨(p, q' + 1), h⟩ => (D.dV p q').comp
      (LinearMap.proj (R := R)
        (φ := fun j : Diag n => D.C j.1.1 j.1.2) ⟨(p, q'), by omega⟩)

def dTot (n : ℕ) :
    Tot D n →ₗ[R] Tot D (n + 1) :=
  LinearMap.pi fun i =>
    dTotH D i + ((-1 : ℤ) ^ i.1.1) • dTotV D i

def HTotB : (n : ℕ) → Submodule R (LinearMap.ker (dTot D n))
  | 0 => ⊥
  | n' + 1 => (LinearMap.range (dTot D n')).comap
      (LinearMap.ker (dTot D (n' + 1))).subtype

abbrev HTot (n : ℕ) : Type u :=
  LinearMap.ker (dTot D n) ⧸ HTotB D n

end Tot

section DTotGeneric

variable {R : Type u} [CommRing R] {D : Bounded R}

theorem dTot_apply_zero_succ {n q' : ℕ} (h : 0 + (q' + 1) = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(0, q' + 1), h⟩ = D.dV 0 q' (c ⟨(0, q'), by omega⟩) := by
  simp only [dTot, LinearMap.pi_apply, LinearMap.add_apply,
    LinearMap.smul_apply, dTotH, dTotV, LinearMap.zero_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, pow_zero, one_smul, zero_add]

theorem dTot_apply_succ_zero {n p' : ℕ} (h : p' + 1 + 0 = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(p' + 1, 0), h⟩ = D.dH p' 0 (c ⟨(p', 0), by omega⟩) := by
  simp only [dTot, LinearMap.pi_apply, LinearMap.add_apply,
    LinearMap.smul_apply, dTotH, dTotV, LinearMap.zero_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, smul_zero, add_zero]

theorem dTot_apply_succ_succ {n p' q' : ℕ} (h : p' + 1 + (q' + 1) = n + 1)
    (c : Tot D n) :
    dTot D n c ⟨(p' + 1, q' + 1), h⟩
      = D.dH p' (q' + 1) (c ⟨(p', q' + 1), by omega⟩)
        + ((-1 : ℤ) ^ (p' + 1)) • D.dV (p' + 1) q' (c ⟨(p' + 1, q'), by omega⟩) := by
  rfl

theorem dTot_comp_dTot (D : Bounded R) (n : ℕ) :
    dTot D (n + 1) ∘ₗ dTot D n = 0 := by
  refine LinearMap.ext fun c => funext fun ⟨⟨pp, q⟩, h⟩ => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply]
  match pp, q, h with
  | 0, 0, h => omega
  | 0, q' + 1, h =>
    obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
    rw [dTot_apply_zero_succ, dTot_apply_zero_succ,
      ← LinearMap.comp_apply, D.dV_sq, LinearMap.zero_apply]
  | p' + 1, 0, h =>
    obtain ⟨p'', rfl⟩ : ∃ p'', p' = p'' + 1 := ⟨p' - 1, by omega⟩
    rw [dTot_apply_succ_zero, dTot_apply_succ_zero,
      ← LinearMap.comp_apply, D.dH_sq, LinearMap.zero_apply]
  | p' + 1, q' + 1, h =>
    rw [dTot_apply_succ_succ]
    have hH : D.dH p' (q' + 1) (dTot D n c ⟨(p', q' + 1), by omega⟩)
        = ((-1 : ℤ) ^ p') • D.dH p' (q' + 1) (D.dV p' q' (c ⟨(p', q'), by omega⟩)) := by
      rcases p' with _ | p''
      · rw [dTot_apply_zero_succ, pow_zero, one_smul]
      · rw [dTot_apply_succ_succ, map_add, map_zsmul,
          ← LinearMap.comp_apply, D.dH_sq, LinearMap.zero_apply, zero_add]
    have hV : D.dV (p' + 1) q' (dTot D n c ⟨(p' + 1, q'), by omega⟩)
        = D.dV (p' + 1) q' (D.dH p' q' (c ⟨(p', q'), by omega⟩)) := by
      rcases q' with _ | q''
      · rw [dTot_apply_succ_zero]
      · rw [dTot_apply_succ_succ, map_add, map_zsmul,
          show D.dV (p' + 1) (q'' + 1) (D.dV (p' + 1) q'' (c ⟨(p' + 1, q''), by omega⟩)) = 0 from
            LinearMap.congr_fun (D.dV_sq (p' + 1) q'') _, smul_zero, add_zero]
    rw [hH, hV,
      show D.dV (p' + 1) q' (D.dH p' q' (c ⟨(p', q'), by omega⟩))
        = D.dH p' (q' + 1) (D.dV p' q' (c ⟨(p', q'), by omega⟩)) from
        LinearMap.congr_fun (D.dHV_comm p' q') _,
      ← add_smul, show ((-1:ℤ)^p' + (-1)^(p'+1)) = 0 from by ring, zero_smul]

end DTotGeneric

section E2

variable {R : Type u} [CommRing R] (D : Bounded R)

def colB (p : ℕ) : (q : ℕ) → Submodule R (LinearMap.ker (D.dV p q))
  | 0 => ⊥
  | q' + 1 => (LinearMap.range (D.dV p q')).comap (LinearMap.ker (D.dV p (q' + 1))).subtype

abbrev colH (p q : ℕ) : Type u :=
  LinearMap.ker (D.dV p q) ⧸ colB D p q

def colHdH (p q : ℕ) :
    colH D p q →ₗ[R] colH D (p + 1) q :=
  Submodule.mapQ _ _
    ((D.dH p q).restrict fun x hx => LinearMap.mem_ker.mpr <| by
      rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply,
        LinearMap.mem_ker.mp hx, map_zero])
    (by
      rcases q with _ | q'
      · simp only [colB]; exact bot_le
      · rintro x ⟨y, hy⟩
        exact ⟨D.dH p q' y, by
          show D.dV (p + 1) q' (D.dH p q' y) = D.dH p (q' + 1) x.1
          rw [← LinearMap.comp_apply, D.dHV_comm, LinearMap.comp_apply, hy]; rfl⟩)

def E₂IB :
    (p q : ℕ) → Submodule R (LinearMap.ker (colHdH D p q))
  | 0, _ => ⊥
  | p' + 1, q => (LinearMap.range (colHdH D p' q)).comap
      (LinearMap.ker (colHdH D (p' + 1) q)).subtype

abbrev E₂I (p q : ℕ) : Type u :=
  LinearMap.ker (colHdH D p q) ⧸ E₂IB D p q

def transpose : Bounded R where
  C a b := D.C b a
  dH a b := D.dV b a
  dV a b := D.dH b a
  dH_sq a b := D.dV_sq b a
  dV_sq a b := D.dH_sq b a
  dHV_comm a b := (D.dHV_comm b a).symm
  N := D.N
  hBound a b h := D.hBound b a h.symm

abbrev E₂II (p q : ℕ) : Type u :=
  E₂I (transpose D) q p

instance (p q : ℕ) : AddCommGroup (E₂I D p q) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))
instance (p q : ℕ) : Module R (E₂I D p q) :=
  inferInstanceAs (Module R (_ ⧸ _))
instance (p q : ℕ) : AddCommGroup (E₂II D p q) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))
instance (p q : ℕ) : Module R (E₂II D p q) :=
  inferInstanceAs (Module R (_ ⧸ _))

end E2

structure SubQuot (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] where
  Z : Submodule R M
  B : Submodule R M
  hBZ : B ≤ Z

abbrev SubQuot.carrier {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (s : SubQuot R M) : Type u := s.Z ⧸ s.B.comap s.Z.subtype

structure Convergence (R : Type u) [CommRing R]
    (E₂ : ℕ → ℕ → Type u) [∀ p q, AddCommGroup (E₂ p q)] [∀ p q, Module R (E₂ p q)]
    (H : ℕ → Type u) [∀ n, AddCommGroup (H n)] [∀ n, Module R (H n)] (N : ℕ) where

  Einf : ∀ p q, SubQuot R (E₂ p q)

  hZ0 : ∀ p, (Einf p 0).Z = ⊤

  Bfilt : ∀ p, Fin (N + 1) → Submodule R (E₂ p 0)
  Bfilt_mono : ∀ p, Monotone (Bfilt p)
  Bfilt_bot : ∀ p, Bfilt p 0 = ⊥
  Bfilt_top : ∀ p, Bfilt p (Fin.last N) = (Einf p 0).B

  Bfilt_gr : ∀ p (i : Fin N), ∃ p' q', 1 ≤ q' ∧ ∃ (s : SubQuot R (E₂ p' q')),
    Nonempty (((Bfilt p i.succ) ⧸ (Bfilt p i.castSucc).comap (Bfilt p i.succ).subtype)
      ≃ₗ[R] s.carrier)

  Hfilt : ∀ n, Fin (N + 2) → Submodule R (H n)
  Hfilt_mono : ∀ n, Monotone (Hfilt n)
  Hfilt_bot : ∀ n, Hfilt n 0 = ⊥
  Hfilt_top : ∀ n, Hfilt n (Fin.last (N + 1)) = ⊤

  Hfilt_gr : ∀ (p : Fin (N + 1)),
    Nonempty (((Hfilt (↑p) p.succ) ⧸ (Hfilt (↑p) p.castSucc).comap (Hfilt (↑p) p.succ).subtype)
      ≃ₗ[R] (Einf p 0).carrier)

def BoundedSpectralSequence : Prop :=
  ∀ (R : Type u) [CommRing R] (D : Bounded R),
    Nonempty (Convergence R (E₂I D) (HTot D) D.N)

end DoubleComplex

end


