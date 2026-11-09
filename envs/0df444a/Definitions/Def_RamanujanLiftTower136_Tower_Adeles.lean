-- Prove2me | Definitions.Def_RamanujanLiftTower136_Tower_Adeles
-- name    : RamanujanLiftTower136_Tower_Adeles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:39:24.817675+00:00
-- url     : https://prove2.me/theorems/999a142e-6c5c-40b6-a467-ee954d2c8363
-- title:
--   Finite quaternionic ideles and the compatible class-coordinate chain
-- statement:
--   A finite quaternionic idele is a tuple of local units integral, together with its inverse, at all but finitely many finite places. Let $U_n$ be the tuples that are units of every completed $E_n$.
--
--   Define the actual double quotient $D^\times\backslash\widehat D^\times/U_n$, the right cosets $U_0/U_n$, and the local cosets $K/K_n$. Here $K$ is the dyadic scalar-modulo-$2$ kernel and $K_n$ is the unit subgroup of the order (3.9). The desired chain is
--   $$\mathrm{Cl}(E_n)\simeq D^\times\backslash\widehat D^\times/U_n\simeq U_0/U_n\simeq K/K_n\simeq\mathbb Z/2^n\mathbb Z.$$
--   The predicate for this chain requires its maps to respect actual ideal and idele representatives, the fixed splitting at $Q$, the fractional-linear coordinate of $0$, and the translation representing each vertex. It also requires compatibility with extending ideals from $E_{n+1}$ to $E_n$ and reducing residues modulo $2^n$.
--
--   **Formalization Note** Integral invertible $2\times2$ matrices congruent to the identity modulo $2$ represent the projective kernel. Quotienting by the level subgroup already removes all invertible scalar matrices, giving the same coset sets. No bijections or class counts are built into the definitions as facts.
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.15 (PDF p.16), §3.7, (3.13). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Ideals

noncomputable section

namespace RamanujanLiftTower136.Tower
open Classical

abbrev LocalUnitTuple := (R : Place) → (LocalD R)ˣ
def localOrderUnit (A : Set D) (R : Place) (x : (LocalD R)ˣ) : Prop :=
  (x : LocalD R) ∈ completed A R ∧ ((x⁻¹ : (LocalD R)ˣ) : LocalD R) ∈ completed A R
abbrev Idele := {g : LocalUnitTuple // {R | ¬localOrderUnit (orderLattice : Set D) R (g R)}.Finite}
def U (n : ℕ) : Set Idele := {g | ∀ R, localOrderUnit (levelOrder n) R (g.val R)}
def doubleRelation (n : ℕ) (g h : Idele) : Prop :=
  ∃ x : Dˣ, ∃ u : Idele, u ∈ U n ∧ ∀ R,
    (h.val R : LocalD R) = localize R (x : D) * (g.val R : LocalD R) * (u.val R : LocalD R)
abbrev DoubleClass (n : ℕ) := Quot (doubleRelation n)
abbrev UZero := {g : Idele // g ∈ U 0}
def uCosetRelation (n : ℕ) (g h : UZero) : Prop :=
  ∃ u : Idele, u ∈ U n ∧ ∀ R,
    (h.val.val R : LocalD R) = (g.val.val R : LocalD R) * (u.val R : LocalD R)
abbrev UCoset (n : ℕ) := Quot (uCosetRelation n)

def K : Set (Matrix (Fin 2) (Fin 2) ℚ_[2])ˣ := {g |
  (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[2]) i j‖ ≤ 1 ∧
    ‖((g⁻¹ : (Matrix (Fin 2) (Fin 2) ℚ_[2])ˣ) : Matrix (Fin 2) (Fin 2) ℚ_[2]) i j‖ ≤ 1) ∧
  ∀ i j, PadicInt.toZModPow 1 (toPadicInt ((g : Matrix (Fin 2) (Fin 2) ℚ_[2]) i j)) =
    if i = j then 1 else 0}
abbrev KElement := {g : (Matrix (Fin 2) (Fin 2) ℚ_[2])ˣ // g ∈ K}
def KLevel (n : ℕ) : Set KElement := {g |
  ((g.val : (Matrix (Fin 2) (Fin 2) ℚ_[2])ˣ) : Matrix (Fin 2) (Fin 2) ℚ_[2]) ∈ dyadicOrder n ∧
  ((g.val⁻¹ : (Matrix (Fin 2) (Fin 2) ℚ_[2])ˣ) : Matrix (Fin 2) (Fin 2) ℚ_[2]) ∈ dyadicOrder n}
def kCosetRelation (n : ℕ) (g h : KElement) : Prop :=
  ∃ u : KElement, u ∈ KLevel n ∧ h.val = g.val * u.val
abbrev KCoset (n : ℕ) := Quot (kCosetRelation n)

def ideleIdeal (n : ℕ) (g : Idele) : Set D :=
  {x | ∀ R, ∃ a ∈ completed (levelOrder n) R, localize R x = (g.val R : LocalD R)*a}
def idealProduct (I A : Set D) : Set D :=
  (Submodule.span OF {z | ∃ x ∈ I, ∃ a ∈ A, z = x*a} : Set D)

/-- Representatives of the named vertex idele in (3.13). -/
def representsVertex (n : ℕ) (t : Vertex n) (g : Idele) : Prop :=
  (∀ R : Place, R.asIdeal ≠ Q → g.val R = 1) ∧
  ∀ R : Place, R.asIdeal = Q → localSplitting R (g.val R : LocalD R) = translation t.val

def coordinateChain : Prop :=
  ∃ (e : ∀ n, ClassSet (levelOrder n) ≃ DoubleClass n)
    (u : ∀ n, DoubleClass n ≃ UCoset n)
    (k : ∀ n, UCoset n ≃ KCoset n)
    (v : ∀ n, KCoset n ≃ Vertex n),
    (∀ n t, locallyPrincipal (levelOrder n) (coordinateIdeal n t)) ∧
    (∀ n (c : ClassSet (levelOrder n)),
      vertexClass n (v n (k n (u n (e n c)))) = c.val) ∧
    (∀ n (g : Idele), locallyPrincipal (levelOrder n) (ideleIdeal n g) ∧
      ∀ c : ClassSet (levelOrder n), c.val = idealClass (ideleIdeal n g) → e n c = Quot.mk _ g) ∧
    (∀ n (g : UZero), u n (Quot.mk _ g.val) = Quot.mk _ g) ∧
    (∀ n (g : UZero) (a : KElement),
      (∀ R : Place, R.asIdeal = Q → localSplitting R (g.val.val R : LocalD R) =
        (a.val : Matrix (Fin 2) (Fin 2) ℚ_[2])) →
      k n (Quot.mk _ g) = Quot.mk _ a) ∧
    (∀ n (a : KElement), v n (Quot.mk _ a) =
      PadicInt.toZModPow n (phi (a.val : Matrix (Fin 2) (Fin 2) ℚ_[2]) 0)) ∧
    (∀ n t, ∃ g : Idele, representsVertex n t g ∧ idealClass (ideleIdeal n g) = vertexClass n t) ∧
    (∀ n t, idealClass (idealProduct (coordinateIdeal (n+1) t) (levelOrder n)) =
      vertexClass n (reduction n t))

end RamanujanLiftTower136.Tower


