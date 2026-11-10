-- Prove2me | Definitions.Def_HighPrecSAC1_Main_Preparation
-- name    : HighPrecSAC1_Main_Preparation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:26:15.477329+00:00
-- url     : https://prove2.me/theorems/5c046c65-c570-4080-ae1a-56fe599a1328
-- title:
--   Rescaling, zero deletion and coefficient truncation in Section 6.1
-- statement:
--   The parameters tau, eta, rho, P and epsilon are explicit. Preliminary words satisfy only the representation and approximation guarantees from Theorem 3.1. Their exponents define power-of-two scale factors. Each monomial occurrence is rescaled, deleted if a zero coordinate is involved, and truncated downward to a multiple of 2^{-P}. Input rows stay unchanged. The exact truncated values and the prescribed b-hat approximation are defined by the construction. The family interface records the source polynomial, logspace and size assumptions without assuming Lemma 6.2.
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Definitions and constructions, §§2, 3, 6, 7, printed p. 27 (PDF 28)

import Definitions.Def_HighPrecSAC1_Main_Recursive

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

def tau (K : ℕ) : ℕ := 6*K+20
noncomputable def eta (K : ℕ) : ℝ := err (tau K)
noncomputable def rho (K : ℕ) : ℝ := eta K / 4
noncomputable def ceilLog (n : ℕ) : ℕ := ⌈lg n⌉₊
noncomputable def truncationBits (K t N : ℕ) : ℕ := K + ceilLog N + max t (tau K) + 10
noncomputable def truncationError (K t N : ℕ) : ℝ :=
  8*N*((2:ℝ)^K-1)*err (truncationBits K t N)

abbrev BarWords (K m : ℕ) := Coord K m → FloatRep

noncomputable def barValues {K m : ℕ} (bar : BarWords K m) : GVec K m := fun v => (bar v).value

/-- Only the guarantees from Theorem 3.1, never any conclusion of Lemma 6.2. -/
noncomputable def BarValid {n : ℕ} (G : PositiveCircuit n) (K b : ℕ)
    (x : Fin n → Bool) (bar : BarWords K G.gates) : Prop :=
  (∀ v, (bar v).Valid (tau K+4) b) ∧
  (∀ j, (bar (0,j)).value = (layered G K x).initial j) ∧
  (1-rho K) • (layered G K x).exact ≤ barValues bar ∧
    barValues bar ≤ (layered G K x).exact

noncomputable def scale {K m : ℕ} (bar : BarWords K m) (v : Coord K m) : ℝ :=
  if v.1.val = 0 ∨ (bar v).zero = true then 1 else (2:ℝ)^(bar v).exponent

noncomputable def scaledExact {n : ℕ} (G : PositiveCircuit n) (K : ℕ)
    (x : Fin n → Bool) (bar : BarWords K G.gates) : GVec K G.gates :=
  fun v => (layered G K x).exact v / scale bar v

noncomputable def QTerm.rescale {m : ℕ} (parent : ℝ) (child : Fin m → ℝ) : QTerm m → QTerm m
  | .const a => .const (a/parent)
  | .lin a j => .lin (a*child j/parent) j
  | .quad a j k => .quad (a*child j*child k/parent) j k

def QTerm.survives {m : ℕ} (zero : Fin m → Bool) : QTerm m → Bool
  | .const _ => true
  | .lin _ j => !(zero j)
  | .quad _ j k => !(zero j) && !(zero k)

noncomputable def QTerm.truncate {m : ℕ} (P : ℕ) : QTerm m → QTerm m
  | .const a => .const (err P * (⌊(2:ℝ)^P*a⌋ : ℝ))
  | .lin a j => .lin (err P * (⌊(2:ℝ)^P*a⌋ : ℝ)) j
  | .quad a j k => .quad (err P * (⌊(2:ℝ)^P*a⌋ : ℝ)) j k

/-- Rescale, delete zero monomials, then truncate each occurrence, in that order (§6.1). -/
noncomputable def prepared {n : ℕ} (G : PositiveCircuit n) (K t N : ℕ)
    (x : Fin n → Bool) (bar : BarWords K G.gates) : LayerSystem K G.gates where
  initial := (layered G K x).initial
  layer := fun i j =>
    let parent : Coord K G.gates := (⟨i.val+1, by omega⟩, j)
    let prev : Fin (K+1) := ⟨i.val, by omega⟩
    if (bar parent).zero then [] else
      (((layered G K x).layer i j).filter (QTerm.survives (fun a => (bar (prev,a)).zero))).map
        (fun a => (a.rescale (scale bar parent) (fun k => scale bar (prev,k))).truncate
          (truncationBits K t N))

noncomputable def preparedApprox {n : ℕ} (G : PositiveCircuit n) (K : ℕ)
    (x : Fin n → Bool) (bar : BarWords K G.gates) : GVec K G.gates :=
  fun v => if v.1.val = 0 then (layered G K x).initial v.2 else
    (1-rho K)*(bar v).value / scale bar v

/-- N ≥ 2 bounds the gates and wires of the copied circuit: it is at least the K+1 gate copies
    and the K copies of every original wire (source-copy and output wires need not be counted). -/
def LayerSizeBound {n : ℕ} (G : PositiveCircuit n) (K N : ℕ) : Prop :=
  2 ≤ N ∧ (K+1)*G.gates + K*(∑ j, (G.gate j).arity) ≤ N

/-- Data shared by the asymptotic representation statements in §6. -/
structure PreparationFamily where
  K : ℕ → ℕ
  t : ℕ → ℕ
  N : ℕ → ℕ
  width : ℕ → ℕ
  circuits : ∀ n, PositiveCircuit n
  bar : ∀ n, (Fin n → Bool) → BarWords (K n) (circuits n).gates

noncomputable def PreparationFamily.valid (D : PreparationFamily) : Prop :=
  Parameter D.K ∧ Parameter D.t ∧ Parameter D.N ∧ Parameter D.width ∧
  AUniform D.circuits ∧ APoly D.circuits ∧
  Bound (fun n => D.width n) (fun n => (D.K n : ℝ) + lg n) ∧
  ∀ n, 1 ≤ n → (D.circuits n).depth ≤ D.K n ∧
    LayerSizeBound (D.circuits n) (D.K n) (D.N n) ∧
    ∀ x, BarValid (D.circuits n) (D.K n) (D.width n) x (D.bar n x)

noncomputable def PreparationFamily.system (D : PreparationFamily) (n : ℕ) (x : Fin n → Bool) :=
  prepared (D.circuits n) (D.K n) (D.t n) (D.N n) x (D.bar n x)

noncomputable def PreparationFamily.bhat (D : PreparationFamily) (n : ℕ) (x : Fin n → Bool) :=
  preparedApprox (D.circuits n) (D.K n) x (D.bar n x)

end HighPrecSAC1.Main


