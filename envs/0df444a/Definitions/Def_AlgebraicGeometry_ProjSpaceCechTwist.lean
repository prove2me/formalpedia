-- Prove2me | Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
-- name    : AlgebraicGeometry_ProjSpaceCechTwist
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/48ef2127-0320-5ed5-9c24-8d95dcd6df91
-- title:
--   Laurent-monomial Čech model for twisting sheaves on projective space
-- statement:
--   Fix a commutative ring $R$, a natural number $n$ and $d \in \mathbb{Z}$. This module sets up an explicit combinatorial model of the alternating Čech complex of $\mathcal{O}(d)$ on $\mathbb{P}^n_R$ for the standard cover by the loci $D_+(x_j)$, $0 \le j \le n$, without constructing any sheaf or scheme. An exponent vector is an element of `Twist.MonExp n` $= (\mathrm{Fin}(n+1) \to \mathbb{Z})$; `Twist.negSupp n a` is the finite set $\{j : a_j < 0\}$. For a finite set $I \subseteq \mathrm{Fin}(n+1)$, `Twist.Mon n d I` is the subtype of those $a$ with $\sum_j a_j = d$ and $\mathrm{negSupp}(a) \subseteq I$, i.e. the Laurent monomials $x^a$ of total degree $d$ whose poles lie among the $x_j$, $j \in I$; `Twist.Mon.incl` is the evident injection along $I \subseteq J$, and `Twist.Sec R n d I` is the free $R$-module $\bigl(\mathrm{Mon}\ n\ d\ I\bigr) \to_0 R$ of finitely supported $R$-combinations of such monomials, the stand-in for $\Gamma\bigl(\bigcap_{j \in I} D_+(x_j), \mathcal{O}(d)\bigr)$.
--
--   The index sets are `Idx n i`, the strictly monotone maps $\mathrm{Fin}(i+1) \to \mathrm{Fin}(n+1)$; these are finite, `Idx.img` is the image of such an $s$, of cardinality $i+1$, and `Idx.face n s j` is $s \circ \mathrm{succAbove}\ j$, the subsequence omitting the $j$-th entry, whose image is contained in that of $s$. The degree-$i$ cochains are `Twist.cochain R n d i` $= \prod_{s : \mathrm{Idx}\ n\ i} \mathrm{Sec}\ R\ n\ d\ (\mathrm{img}\ s)$, an $R$-module, and the differential `Twist.d` is the $R$-linear map given componentwise by $(d^i f)(s) = \sum_{j : \mathrm{Fin}(i+2)} (-1)^j\,\mathrm{faceRes}(f(\mathrm{face}\ s\ j))$, where `Twist.faceRes` is the map on finitely supported functions induced by the monomial inclusion; `Twist.d_apply` records this formula. Cohomology `Twist.H R n d i` is defined by cases: for $i = 0$ the kernel of $d^0$, and for $i+1$ the quotient of $\ker d^{i+1}$ by the preimage in it of $\operatorname{im} d^{i}$, each carrying its $R$-module structure. Auxiliary results are the simplicial identity $\mathrm{succAbove}(j.\mathrm{succ}) \circ \mathrm{succAbove}\ i = \mathrm{succAbove}(i.\mathrm{castSucc}) \circ \mathrm{succAbove}\ j$ for $i \le j$, the injectivity of the monomial inclusions, and the facts that `Idx n i` is empty and hence `Twist.cochain R n d i` is a subsingleton when $n < i$.
--
--   **Relation to Mathlib.** This is the project's own hand-built complex rather than an instance of Mathlib's sheaf-theoretic Čech machinery: the cochain modules, the differential and the cohomology are defined directly on finitely supported functions on monomial index types, with `Finsupp.lmapDomain`, `LinearMap.pi` and `LinearMap.proj` as ingredients, and `Twist.H` is a bespoke kernel/quotient rather than Mathlib's homology of a chain complex.
--
--   **Where it is used.** This monomial model is the complex on which the computation of $H^i(\mathbb{P}^n_R, \mathcal{O}(d))$ is carried out (finiteness, and vanishing in the relevant degrees), and it provides the index combinatorics shared with the Čech complex of a finitely generated graded module, en route to the coherent-cohomology input needed for the modular curves and Galois-representation arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ProjSpaceCechTwist.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open Finset Function

namespace ProjSpaceCech

theorem Idx.succAbove_comp_succAbove {n : ℕ} {i j : Fin (n + 2)} (H : i ≤ j) :
    Fin.succAbove j.succ ∘ Fin.succAbove i
      = Fin.succAbove i.castSucc ∘ Fin.succAbove j := by
  ext k
  simp only [Function.comp_apply, Fin.succAbove]
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩; rcases k with ⟨k, hk⟩
  simp only [Fin.le_def] at H
  simp only [Fin.lt_def, Fin.castSucc_mk, Fin.succ_mk, Fin.val_succ, Fin.val_castSucc]
  split_ifs <;> simp_all only [Fin.val_succ, Fin.val_castSucc] <;> omega

section Setup

variable (n : ℕ)

abbrev Twist.MonExp := Fin (n + 1) → ℤ

def Twist.negSupp (a : Twist.MonExp n) : Finset (Fin (n + 1)) :=
  univ.filter (fun j => a j < 0)

theorem Twist.mem_negSupp {a : Twist.MonExp n} {j : Fin (n + 1)} :
    j ∈ Twist.negSupp n a ↔ a j < 0 := by
  simp [Twist.negSupp]

def Twist.Mon (d : ℤ) (I : Finset (Fin (n + 1))) : Type :=
  {a : Twist.MonExp n // ∑ j, a j = d ∧ Twist.negSupp n a ⊆ I}

instance Twist.Mon.instDecidableEq (d : ℤ) (I : Finset (Fin (n + 1))) :
    DecidableEq (Twist.Mon n d I) := Classical.decEq _

def Twist.Mon.incl (d : ℤ) {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) :
    Twist.Mon n d I → Twist.Mon n d J :=
  fun a => ⟨a.1, a.2.1, a.2.2.trans hIJ⟩

theorem Twist.Mon.incl_injective (d : ℤ) {I J : Finset (Fin (n + 1))}
    (hIJ : I ⊆ J) : Function.Injective (Twist.Mon.incl n d hIJ) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  exact Subtype.ext (Subtype.mk.inj h)

theorem Twist.Mon.incl_val (d : ℤ) {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J)
    (a : Twist.Mon n d I) :
    (Twist.Mon.incl n d hIJ a).1 = a.1 := rfl

abbrev Twist.Sec (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (I : Finset (Fin (n + 1))) : Type u :=
  Twist.Mon n d I →₀ R

end Setup

section AltCech

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

def Idx (i : ℕ) : Type := {s : Fin (i + 1) → Fin (n + 1) // StrictMono s}

instance Idx.instFintype (i : ℕ) : Fintype (Idx n i) := Subtype.fintype _

instance Idx.instDecidableEq (i : ℕ) : DecidableEq (Idx n i) := Classical.decEq _

def Idx.img {i : ℕ} (s : Idx n i) : Finset (Fin (n + 1)) :=
  Finset.univ.image s.1

theorem Idx.card_img {i : ℕ} (s : Idx n i) :
    (Idx.img n s).card = i + 1 := by
  rw [Idx.img, Finset.card_image_of_injective _ s.2.injective,
    Finset.card_univ, Fintype.card_fin]

def Idx.face {i : ℕ} (s : Idx n (i + 1)) (j : Fin (i + 2)) :
    Idx n i :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

theorem Idx.img_face_subset {i : ℕ} (s : Idx n (i + 1))
    (j : Fin (i + 2)) :
    Idx.img n (Idx.face n s j) ⊆ Idx.img n s := by
  intro x hx
  simp only [Idx.img, Idx.face, mem_image, mem_univ, true_and] at *
  obtain ⟨k, hk⟩ := hx
  exact ⟨Fin.succAbove j k, hk⟩

def Twist.faceRes {i : ℕ} (s : Idx n (i + 1)) (j : Fin (i + 2)) :
    Twist.Sec R n d (Idx.img n (Idx.face n s j))
      →ₗ[R] Twist.Sec R n d (Idx.img n s) :=
  Finsupp.lmapDomain R R (Twist.Mon.incl n d (Idx.img_face_subset n s j))

abbrev Twist.cochain (i : ℕ) : Type u :=
  ∀ s : Idx n i, Twist.Sec R n d (Idx.img n s)

instance Twist.cochain.instAddCommGroup (i : ℕ) : AddCommGroup (Twist.cochain R n d i) :=
  inferInstanceAs (AddCommGroup (∀ s, _ →₀ R))

instance Twist.cochain.instModule (i : ℕ) : Module R (Twist.cochain R n d i) :=
  inferInstanceAs (Module R (∀ s, _ →₀ R))

end AltCech

def Twist.d (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (i : ℕ) :
    Twist.cochain R n d i →ₗ[R] Twist.cochain R n d (i + 1) :=
  LinearMap.pi fun s => ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((Twist.faceRes R n d s j).comp (LinearMap.proj (Idx.face n s j)))

section AltCech

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

theorem Twist.d_apply (i : ℕ) (f : Twist.cochain R n d i)
    (s : Idx n (i + 1)) :
    Twist.d R n d i f s =
      ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        Twist.faceRes R n d s j (f (Idx.face n s j)) := by
  simp only [Twist.d, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem Idx.isEmpty_of_lt {i : ℕ} (hi : n < i) :
    IsEmpty (Idx n i) := by
  rw [Idx, isEmpty_subtype]
  intro s hs
  have := Fintype.card_le_of_injective s hs.injective
  simp only [Fintype.card_fin] at this; omega

theorem Twist.cochain_subsingleton_of_lt {i : ℕ} (hi : n < i) :
    Subsingleton (Twist.cochain R n d i) := by
  have := Idx.isEmpty_of_lt n hi
  exact ⟨fun f g => funext fun s => (this.false s).elim⟩

end AltCech

section Cohomology

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

def Twist.H : ℕ → Type u
  | 0 => LinearMap.ker (Twist.d R n d 0)
  | (i + 1) =>
      LinearMap.ker (Twist.d R n d (i + 1)) ⧸
        (LinearMap.range (Twist.d R n d i)).comap
          (LinearMap.ker (Twist.d R n d (i + 1))).subtype

instance Twist.H.addCommGroup (i : ℕ) : AddCommGroup (Twist.H R n d i) :=
  match i with
  | 0 => inferInstanceAs (AddCommGroup
      ↥(LinearMap.ker (Twist.d R n d 0)))
  | (j + 1) => inferInstanceAs (AddCommGroup
      (↥(LinearMap.ker (Twist.d R n d (j + 1))) ⧸ _))

instance Twist.H.module (i : ℕ) : Module R (Twist.H R n d i) :=
  match i with
  | 0 => inferInstanceAs (Module R
      ↥(LinearMap.ker (Twist.d R n d 0)))
  | (j + 1) => inferInstanceAs (Module R
      (↥(LinearMap.ker (Twist.d R n d (j + 1))) ⧸ _))

end Cohomology

end ProjSpaceCech

end


