-- Prove2me | Definitions.Def_PPSLattice_FigParts
-- name    : PPSLattice_FigParts
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:31:12.158975+00:00
-- url     : https://prove2.me/theorems/0918765c-5970-4a21-89db-c372c84f7462
-- title:
--   Static/dynamic output decomposition and append compilers for Figure 1
-- statement:
--   For Figure 1, the output $(c,P,d,h)$ is decomposed into the hardwired prefix $(c,P)$ and the suffix $(d,h)$. Only $d$ depends on the circuit input $b$:
--   $$d_j=\sum_t s_t(\mathbf B\,\mathbf G^{-1}(\mathbf P))_{tj}-\sum_t s_tP_{tj}+\tilde e_j+tg_j,$$
--   where $\mathbf B$ is decoded from $b$. Thus its coefficients are hardwired linear forms in the decoded entries of $\mathbf B$, while $c$, $P$, and $h$ are static strings.
--
--   The module proves `figOut = figPartAdd figPreOut figDynamicOut`. `FigPartCompilerValid` is the same uniform compiler contract as `FigCompilerValid`, restricted to a specified output part: `PolyTimeOn` for the circuit description and the unary size bound, a size independent of all hardwired data, and exact evaluation. `joinFigCompiler` sequentially evaluates two circuits on the same input of length `figInputLen` and appends their outputs; its size is the sum of the two sizes. This supplies the static-output and append machinery for Claim 4.11 without hiding any TM2 polynomial-time obligation.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission #1347 (manuscript sha256 7f9c493f…), Figure 1 and Remark 4.9, p.22; Claim 4.11, p.22; Construction 4.6, p.21.

import Mathlib
import Definitions.Def_PPSLattice_FigCompilerValid
import Definitions.Def_PPSLattice_FigCircuitOps
import Definitions.Def_PPSLattice_decBin
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- Fixed-width encoding of a list of field elements, starting at randomness index `base`. -/
def encElems (q lam base : ℕ) (r : List ℕ) (xs : List (ZMod q)) : Str :=
  (xs.mapIdx fun j x => AvoidPlast.fixedBits (Nat.clog 2 q + lam)
    (x.val + q * r.getD (base + j) 0)).flatten

/-- The arithmetic of the input-dependent `d` block of Figure 1. -/
def figD (q n m lam : ℕ) (s : Fin n → ZMod q)
    (P : Matrix (Fin n) (Fin lam) (ZMod q)) (et tg : Fin lam → ZMod q)
    (b : Str) (j : Fin lam) : ZMod q :=
  (∑ t, s t * ((decMat q n m b * gadgetInv q n m P) t j)) -
    (∑ t, s t * P t j) + et j + tg j

/-- The input-independent prefix `(c,P)` of Figure 1, encoded as in Remark 4.9. -/
def figPreOut (q n m N lam : ℕ)
    (A : Matrix (Fin n) (Fin (Nat.clog 2 N * m)) (ZMod q))
    (s : Fin n → ZMod q) (e : Fin (Nat.clog 2 N * m) → ZMod q)
    (P : Matrix (Fin n) (Fin lam) (ZMod q)) (_et _tg : Fin lam → ZMod q)
    (i : ℕ) (_mu : Str) (r : List ℕ) (_b : Str) : Str :=
  let c : Fin (Nat.clog 2 N * m) → ZMod q := fun j =>
    (∑ t, s t * (A - kronG q n m (Nat.clog 2 N) (encvec N i)) t j) + e j
  let pre : List (ZMod q) := List.ofFn c ++
    List.ofFn (fun t : Fin (n * lam) => P (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)
  encElems q lam 0 r pre

/-- The suffix `(d,h)` of Figure 1: `d` is input-dependent and `h` is hardwired. -/
def figDynamicOut (q n m N lam : ℕ)
    (_A : Matrix (Fin n) (Fin (Nat.clog 2 N * m)) (ZMod q))
    (s : Fin n → ZMod q) (_e : Fin (Nat.clog 2 N * m) → ZMod q)
    (P : Matrix (Fin n) (Fin lam) (ZMod q)) (et tg : Fin lam → ZMod q)
    (_i : ℕ) (mu : Str) (r : List ℕ) (b : Str) : Str :=
  let h : Str := List.ofFn fun j : Fin lam => xor (round2 (tg j)) (mu.getD j false)
  encElems q lam (Nat.clog 2 N * m + n * lam) r (List.ofFn (figD q n m lam s P et tg b)) ++ h

private lemma encElems_append (q lam : ℕ) (r : List ℕ) (xs ys : List (ZMod q)) :
    encElems q lam 0 r (xs ++ ys) = encElems q lam 0 r xs ++ encElems q lam xs.length r ys := by
  unfold encElems
  rw [List.mapIdx_append, List.flatten_append]
  congr 1
  simp only [zero_add, Nat.add_comm]

/-- Figure 1's output is its static `(c,P)` prefix followed by its `(d,h)` suffix. -/
theorem figOut_eq_pre_append_dynamic (q n m N lam : ℕ)
    (A : Matrix (Fin n) (Fin (Nat.clog 2 N * m)) (ZMod q))
    (s : Fin n → ZMod q) (e : Fin (Nat.clog 2 N * m) → ZMod q)
    (P : Matrix (Fin n) (Fin lam) (ZMod q)) (et tg : Fin lam → ZMod q)
    (i : ℕ) (mu : Str) (r : List ℕ) (b : Str) :
    figOut q n m N lam A s e P et tg i mu r b =
      figPreOut q n m N lam A s e P et tg i mu r b ++
        figDynamicOut q n m N lam A s e P et tg i mu r b := by
  unfold figOut figPreOut figDynamicOut figD encElems
  simp [List.mapIdx_append, List.flatten_append, List.append_assoc,
    Nat.add_comm, Nat.add_assoc]

/-- The common dependent type of Figure-1 output functions and their parts. -/
abbrev FigFun :=
  (q n m N lam : ℕ) →
    Matrix (Fin n) (Fin (Nat.clog 2 N * m)) (ZMod q) →
    (Fin n → ZMod q) → (Fin (Nat.clog 2 N * m) → ZMod q) →
    Matrix (Fin n) (Fin lam) (ZMod q) → (Fin lam → ZMod q) → (Fin lam → ZMod q) →
    ℕ → Str → List ℕ → Str → Str

/-- Concatenate two output functions on the same hardwired data and circuit input. -/
def figPartAdd (F G : FigFun) : FigFun :=
  fun q n m N lam A s e P et tg i mu r b =>
    F q n m N lam A s e P et tg i mu r b ++ G q n m N lam A s e P et tg i mu r b

/-- Function-level form of the prefix/suffix decomposition. -/
theorem figOut_eq_figPartAdd : figOut = figPartAdd figPreOut figDynamicOut := by
  funext q n m N lam A s e P et tg i mu r b
  exact figOut_eq_pre_append_dynamic q n m N lam A s e P et tg i mu r b

/-- A polynomial-time compiler for one part of Figure 1, with its uniform size bound. -/
def FigPartCompilerValid (F : FigFun) (K : Str → RestrictedDec.Circuit)
    (sC : ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  PolyTimeOn (fun w : Str => w) (fun w => (K w).code) ∧
    PolyTimeOn (fun a : ℕ × ℕ × ℕ × ℕ =>
        BeyondDS.tup [encNat a.1, encBin a.2.1, encNat a.2.2.1, encBin a.2.2.2])
      (fun a => encNat (sC a.1 a.2.1 a.2.2.1 a.2.2.2)) ∧
    ∀ (lam N n q : ℕ), q.Prime →
      ∀ (A : Matrix (Fin n) (Fin (Nat.clog 2 N * (n * Nat.clog 2 q))) (ZMod q))
        (s : Fin n → ZMod q) (e : Fin (Nat.clog 2 N * (n * Nat.clog 2 q)) → ZMod q)
        (P : Matrix (Fin n) (Fin lam) (ZMod q)) (et tg : Fin lam → ZMod q) (i : ℕ) (mu : Str)
        (r : List ℕ),
        i ∈ Finset.Icc 1 N → mu.length = lam →
        r.length = Nat.clog 2 N * (n * Nat.clog 2 q) + n * lam + lam →
        (∀ x ∈ r, x < 2 ^ (Nat.clog 2 q + lam) / q) →
          circSize (K (figCode lam N n q A s e P et tg i mu r)) ≤ sC lam N n q ∧
            ∀ b : Str, b.length = n * (n * Nat.clog 2 q) * Nat.clog 2 q →
              (K (figCode lam N n q A s e P et tg i mu r)).eval b =
                F q n (n * Nat.clog 2 q) N lam A s e P et tg i mu r b

/-- The number of input bits, read from the unary `n` and binary `q` fields of a Figure-1 code. -/
def figInputLen (w : Str) : ℕ :=
  let fs := BeyondDS.untup w
  let n := BeyondDS.decNat (fs.getD 2 [])
  let q := decBin (fs.getD 3 [])
  n * (n * Nat.clog 2 q) * Nat.clog 2 q

/-- Sequential assembly of two compilers for consecutive output parts. -/
def joinFigCompiler (K₁ K₂ : Str → RestrictedDec.Circuit) (w : Str) : RestrictedDec.Circuit :=
  appendCircuit (figInputLen w) (K₁ w) (K₂ w)

/-- The size function of the sequential assembly. -/
def joinFigSize (s₁ s₂ : ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ :=
  fun lam N n q => s₁ lam N n q + s₂ lam N n q

/-- The generic part predicate specializes to the published compiler predicate. -/
theorem figPartCompilerValid_figOut (K : Str → RestrictedDec.Circuit)
    (sC : ℕ → ℕ → ℕ → ℕ → ℕ) :
    FigPartCompilerValid figOut K sC ↔ FigCompilerValid K sC := Iff.rfl

end PPSLattice


