-- Prove2me | Definitions.Def_SparseCCE_ThreePlayer_ReferenceProfile
-- name    : SparseCCE_ThreePlayer_ReferenceProfile
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:06:55.807403+00:00
-- url     : https://prove2.me/theorems/5b8189fc-ba22-4b1c-933d-2f86e13b6182
-- title:
--   Laws of recommended transcripts, partner choices, the reference laws $\hat\nu$ and the reference profile
-- statement:
--   Let $\mu$ be a law of action profiles of a normal-form game whose actions $b_j\in B_j$ contain transcripts $\mathrm{tr}_j(b_j)\in Z_j$. $\nu_j$ is the law of $j$'s recommended transcript, $\nu_{ik}$ the joint law of those of $i$ and $k$, and $\nu_{ik}(\cdot\mid z_k=\tilde z)$ the conditional law.
--
--   A **partner choice** $k$ has $k_i\neq i$ and every pair of distinct players of the form $\{i,k_i\}$. $C_i$ is the set of conditional laws $\nu_{ik_i}(\cdot\mid z_{k_i}=\tilde z)$ with $\nu_{k_i}(\tilde z)\ge M^{-2}$, $r_i=\dim\operatorname{span}C_i$.
--
--   Laws $\hat\nu$ are **reference laws** of $\mu$ if for every $i$ there are a dominating family $c_1,\dots,c_{r_i}$ of $C_i$ (the laws of Lemma 3.2), a repaired law $\bar\nu_i^c$ of $\bar\nu_i=\frac1{r_i}\sum_sc_s$ and a repaired law $\nu_i^c$ of $\nu_i$, with $\hat\nu_i=(\bar\nu_i^c+\nu_i^c+\mathrm{unif}_i)/3$. A **reference profile** is a profile of decodings of reference laws.
--
--   For the computability clause, enumerations of players, outcomes, signals and actions code transcripts (`trCode`), and `refInput` is the algorithm's input: $M$ in unary, the sizes, partners, the transcript of each normal-form action, and $\mu$ by rational weights and components. `IsListing`/`IsLawListing` describe a listing of a finite table in some order.
--
--   `refTableInput` also codes a rational probability table of $\mu$, in the mixed-radix order of the supplied player and action enumerations. Sparsity is a promise over real product distributions; no rational factorization is required for this input format.
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). §3.3, Lemma 3.5, p. 17; App. A.3, pp. 30–31.

import Mathlib
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm
import Definitions.Def_SparseCCE_ThreePlayer_Transcripts
import Definitions.Def_SparseCCE_ThreePlayer_Domination

noncomputable section

namespace SparseCCE.ThreePlayer

open scoped BigOperators

/-- `k` is a partner choice (Lemma 3.5, p. 17): `k_i ≠ i` for every player, and every pair of
distinct players has the form `{i, k_i}`. -/
def IsPartnerChoice {ι : Type} (k : ι → ι) : Prop :=
  (∀ i, k i ≠ i) ∧ ∀ i l, i ≠ l → ∃ a, (a = i ∧ k a = l) ∨ (a = l ∧ k a = i)

namespace RepeatedGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : RepeatedGame ι)
  {B : ι → Type} [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]

/-! ### Laws of recommended transcripts (§3.3, p. 17)

`μ` is a law of action profiles of a normal-form game in which every action `b_j ∈ B_j`
contains a transcript `tr j b_j ∈ Z_j`. -/

/-- `ν_j`: the law of player `j`'s recommended transcript under `μ`. -/
def recLaw (tr : (j : ι) → B j → Γ.Transcript j) (μ : ((j : ι) → B j) → ℝ) (j : ι) :
    Γ.Transcript j → ℝ :=
  fun z => ∑ b, if tr j (b j) = z then μ b else 0

/-- `ν_{ik}`: the joint law of the recommended transcripts of players `i` and `k` under `μ`. -/
def recPairLaw (tr : (j : ι) → B j → Γ.Transcript j) (μ : ((j : ι) → B j) → ℝ) (i k : ι) :
    Γ.Transcript i → Γ.Transcript k → ℝ :=
  fun z z' => ∑ b, if tr i (b i) = z ∧ tr k (b k) = z' then μ b else 0

/-- The conditional law `ν_{ik}(· | z_k = z̃)` of `i`'s transcript given `k`'s. -/
def condLaw (tr : (j : ι) → B j → Γ.Transcript j) (μ : ((j : ι) → B j) → ℝ) (i k : ι)
    (z' : Γ.Transcript k) : Γ.Transcript i → ℝ :=
  fun z => Γ.recPairLaw tr μ i k z z' / Γ.recLaw tr μ k z'

/-- The set `C_i` of Lemma 3.5 (p. 17): the conditional laws `ν_{i k}(· | z_k = z̃)` with
`ν_k(z̃) ≥ M^{-2}`, for the partner `k = k_i`. -/
def condSet (tr : (j : ι) → B j → Γ.Transcript j) (μ : ((j : ι) → B j) → ℝ) (i k : ι) :
    Finset (Γ.Transcript i → ℝ) :=
  (Finset.univ.filter (fun z' : Γ.Transcript k =>
      ((Γ.Mmax : ℝ) ^ 2)⁻¹ ≤ Γ.recLaw tr μ k z')).image (Γ.condLaw tr μ i k)

/-- `r = dim span C_i`, the dimension of the linear span of `C_i` (Lemma 3.2). -/
def condRank (tr : (j : ι) → B j → Γ.Transcript j) (μ : ((j : ι) → B j) → ℝ) (i k : ι) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (↑(Γ.condSet tr μ i k) : Set (Γ.Transcript i → ℝ)))

/-- `ν̂` are the laws of Lemma 3.5 (p. 17) built from `μ` with the partners `k`: for every player
`i`, with `C_i` the conditional laws above, `ν̄_i` is the average of `r = dim span C_i` laws of
`C_i` given by Lemma 3.2, and `ν̂_i = (ν̄_i^c + ν_i^c + unif_i)/3`, where `·^c` is the repaired
law of Lemma A.2. Lemma 3.2's laws and the answer laws of the repairs at probability-zero
prefixes are any admissible choice. -/
def IsReferenceLaws (tr : (j : ι) → B j → Γ.Transcript j) (μ : ((j : ι) → B j) → ℝ) (k : ι → ι)
    (νhat : (j : ι) → Γ.Transcript j → ℝ) : Prop :=
  ∀ i, ∃ c : Fin (Γ.condRank tr μ i (k i)) → Γ.Transcript i → ℝ,
    IsDominatingFamily (Γ.condSet tr μ i (k i)) (Γ.condRank tr μ i (k i)) c ∧
    ∃ nbarC nC : Γ.Transcript i → ℝ,
      Γ.IsRepair (fun z => (1 / (Γ.condRank tr μ i (k i) : ℝ)) * ∑ s, c s z) nbarC ∧
      Γ.IsRepair (Γ.recLaw tr μ i) nC ∧
      νhat i = fun z => (nbarC z + nC z + Γ.unifLaw i z) / 3

/-- `x` is a reference profile of `μ` (Lemma 3.5, p. 17): the profile of the decodings of the laws
`ν̂_j`. -/
def IsReferenceProfile (tr : (j : ι) → B j → Γ.Transcript j) (μ : ((j : ι) → B j) → ℝ)
    (k : ι → ι) (x : Γ.StrategyProfile) : Prop :=
  ∃ νhat, Γ.IsReferenceLaws tr μ k νhat ∧ ∀ j, Γ.IsDecoding (νhat j) (x j)

/-! ### Encodings for the computability clause of Lemma 3.5

Lemma 3.5's construction only uses the transcript structure, so its input and output refer to
outcomes, signals, actions, players and normal-form actions through enumerations `E`. -/

/-- Enumerations of the players, outcomes, signals and actions of `Γ`. -/
structure Enumeration where
  eι : ι ≃ Fin (Fintype.card ι)
  eO : Γ.P.Outcome ≃ Fin (Fintype.card Γ.P.Outcome)
  eΘ : (j : ι) → Γ.P.Θ j ≃ Fin (Fintype.card (Γ.P.Θ j))
  eA : (j : ι) → Γ.P.A j ≃ Fin (Fintype.card (Γ.P.A j))

variable {Γ}

/-- The code of a query: a flag and the outcome's index (from round 2 on), then the signal's
index. -/
def Enumeration.queryCode (E : Γ.Enumeration) {j : ι} (q : Γ.Query j) : List Bool :=
  (match q.1 with
    | none => [false]
    | some o => true :: QAlgorithms.LocalHamiltonian.encBin (E.eO o)) ++
    QAlgorithms.LocalHamiltonian.encBin (E.eΘ j q.2)

/-- The code of a transcript: round by round, its query and the index of its answer. -/
def Enumeration.trCode (E : Γ.Enumeration) {j : ι} (z : Γ.Transcript j) : List Bool :=
  (List.finRange Γ.H).flatMap (fun h =>
    E.queryCode (z.1 h).1 ++ QAlgorithms.LocalHamiltonian.encBin (E.eA j (z.1 h).2))

end RepeatedGame

/-- `s` lists the finite set `K` with a code `key k` and a value code `val k` for every element,
each element exactly once, in some order, preceded by the number of entries. -/
def IsListing {K : Type} [Fintype K] (key val : K → List Bool) (s : List Bool) : Prop :=
  ∃ l : List K, l.Nodup ∧ (∀ k, k ∈ l) ∧
    s = QAlgorithms.LocalHamiltonian.encBin l.length ++ l.flatMap (fun k => key k ++ val k)

/-- `s` lists the rational law (or table) `q` on the finite set `K`, keyed by `key`. -/
def IsLawListing {K : Type} [Fintype K] (key : K → List Bool) (q : K → ℚ) (s : List Bool) : Prop :=
  IsListing key (fun k => QAlgorithms.LocalHamiltonian.encRat (q k)) s

/-- `M` in unary: the padding that lets "time polynomial in `M`" be polynomial time in the length
of the input. -/
def unary (M : ℕ) : List Bool := List.replicate M true

namespace RepeatedGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : RepeatedGame ι}
  {B : ι → Type} [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]

/-- The input of the algorithm of Lemma 3.5: `M` in unary; the sizes `|ι|, H, |O|`; for every
player `j` (in the order of `E.eι`) the sizes `|Θ_j|, |A_j|`, the index of its partner `k_j`;
for every player its action count `|B_j|` and the transcript code of each of its actions (in the
order of `eB j`); and the `T`-sparse law `μ` by its weights and components (`encRatVec`). -/
def refInput (E : Γ.Enumeration) (tr : (j : ι) → B j → Γ.Transcript j)
    (eB : (j : ι) → B j ≃ Fin (Fintype.card (B j))) (k : ι → ι) {T : ℕ} (w : Fin T → ℚ)
    (p : Fin T → (j : ι) → B j → ℚ) : List Bool :=
  unary Γ.Mmax ++ QAlgorithms.LocalHamiltonian.encBin (Fintype.card ι) ++
    QAlgorithms.LocalHamiltonian.encBin Γ.H ++
    QAlgorithms.LocalHamiltonian.encBin (Fintype.card Γ.P.Outcome) ++
    (List.finRange (Fintype.card ι)).flatMap (fun jj =>
      QAlgorithms.LocalHamiltonian.encBin (Fintype.card (Γ.P.Θ (E.eι.symm jj))) ++
      QAlgorithms.LocalHamiltonian.encBin (Fintype.card (Γ.P.A (E.eι.symm jj))) ++
      QAlgorithms.LocalHamiltonian.encBin (E.eι (k (E.eι.symm jj)))) ++
    (List.finRange (Fintype.card ι)).flatMap (fun jj =>
      QAlgorithms.LocalHamiltonian.encBin (Fintype.card (B (E.eι.symm jj))) ++
      (List.finRange (Fintype.card (B (E.eι.symm jj)))).flatMap (fun a =>
        E.trCode (tr (E.eι.symm jj) ((eB (E.eι.symm jj)).symm a)))) ++
    QAlgorithms.LocalHamiltonian.encBin T ++ CardinalMatching.encRatVec T w ++
    (List.finRange T).flatMap (fun t => (List.finRange (Fintype.card ι)).flatMap (fun jj =>
      CardinalMatching.encRatVec (Fintype.card (B (E.eι.symm jj)))
        (fun a => p t (E.eι.symm jj) ((eB (E.eι.symm jj)).symm a))))

/-- Table representation of the input of Lemma 3.5 (pp. 13, 19): the same structural
header as `refInput`, followed by `T` and the rational probability table of `μ` in the
mixed-radix order supplied by `eB`. No rational factorization of this table is required. -/
def refTableInput (E : Γ.Enumeration) (tr : (j : ι) → B j → Γ.Transcript j)
    (eB : (j : ι) → B j ≃ Fin (Fintype.card (B j))) (k : ι → ι) (T : ℕ)
    (μ : ((j : ι) → B j) → ℚ) : List Bool :=
  unary Γ.Mmax ++ QAlgorithms.LocalHamiltonian.encBin (Fintype.card ι) ++
    QAlgorithms.LocalHamiltonian.encBin Γ.H ++
    QAlgorithms.LocalHamiltonian.encBin (Fintype.card Γ.P.Outcome) ++
    (List.finRange (Fintype.card ι)).flatMap (fun jj =>
      QAlgorithms.LocalHamiltonian.encBin (Fintype.card (Γ.P.Θ (E.eι.symm jj))) ++
      QAlgorithms.LocalHamiltonian.encBin (Fintype.card (Γ.P.A (E.eι.symm jj))) ++
      QAlgorithms.LocalHamiltonian.encBin (E.eι (k (E.eι.symm jj)))) ++
    (List.finRange (Fintype.card ι)).flatMap (fun jj =>
      QAlgorithms.LocalHamiltonian.encBin (Fintype.card (B (E.eι.symm jj))) ++
      (List.finRange (Fintype.card (B (E.eι.symm jj)))).flatMap (fun a =>
        E.trCode (tr (E.eι.symm jj) ((eB (E.eι.symm jj)).symm a)))) ++
    QAlgorithms.LocalHamiltonian.encBin T ++
    CardinalMatching.encRatVec (∏ jj : Fin (Fintype.card ι), Fintype.card (B (E.eι.symm jj)))
      (fun a => μ (fun j => (eB j).symm (Fin.cast (by simp)
        ((finPiFinEquiv (n := fun jj => Fintype.card (B (E.eι.symm jj)))).symm a (E.eι j)))))

end RepeatedGame

end SparseCCE.ThreePlayer


