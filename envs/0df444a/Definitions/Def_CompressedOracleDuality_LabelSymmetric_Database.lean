-- Prove2me | Definitions.Def_CompressedOracleDuality_LabelSymmetric_Database
-- name    : CompressedOracleDuality_LabelSymmetric_Database
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:00:42.403956+00:00
-- url     : https://prove2.me/theorems/18830552-3f02-4595-b0e1-56dda30242f1
-- title:
--   Valid compressed databases, Gram matrices and collision-free statistics
-- statement:
--   A database $D$ maps every input to a label or to $\bot$, represented by an absent value. Its support contains just the recorded inputs; its range contains just the recorded labels, excluding $\bot$. Its size is its support cardinality. It is collision-free when equal recorded labels have equal inputs. Relabeling applies an arbitrary label permutation and fixes $\bot$.
--
--   A vector is valid when, in each cell and with the other cells fixed, the sum of its coordinates over the $N$ actual labels is zero. An operator is valid when every image vector is valid. Support at size $t$ means that every matrix entry with either database larger than $t$ vanishes. Matrix label symmetry is simultaneous invariance of both indices under relabeling.
--
--   For the compressed run, let $B_{z,D}$ be its amplitude at $(z,D)$ and set $G=B^\dagger B$. For positive semidefinite $G$ set $R=\sqrt G$ and
--   $$p(\widetilde D,D)=|R_{\widetilde D,D}|^2,\qquad C(G)=\sum_{D:\mathrm{CF}(D)}|D|G_{D,D}.$$
--   The matched and unmatched counts are the expectations, under this joint law, of $1_{\mathrm{CF}(D)}|\operatorname{range}(D)\cap\operatorname{range}(\widetilde D)|$ and $1_{\mathrm{CF}(D)}|\operatorname{range}(D)\setminus\operatorname{range}(\widetilde D)|$. The information is the finite Shannon mutual information in bits. No collision-free restriction is imposed on $\widetilde D$.
--
--   These are mathematical definitions, with no capacity estimate built into them. Square roots are used only under positivity hypotheses in the theorems; diagonal entries of a positive semidefinite matrix are real, so taking their real parts changes no value.
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94, SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, pp. 13–15, (19)–(24), Definitions 3.1–3.2; pp. 20–23, (50), Definition 4.3, (59)

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Model
import Definitions.Def_QAlgorithms_Defs_CompressedOracle
import Definitions.Def_QAlgorithms_Defs_QuantumInformation

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric

abbrev Database (n : ℕ) := Input n → Option (Label n)
abbrev DBMatrix (n : ℕ) := Matrix (Database n) (Database n) ℂ

/-- §2.3: bottom is an unrecorded cell, and is excluded from support and range. -/
def dbSupport {n : ℕ} (D : Database n) : Finset (Input n) :=
  open Classical in Finset.univ.filter (fun x => D x ≠ none)
def dbSize {n : ℕ} (D : Database n) : ℕ := (dbSupport D).card
def dbRange {n : ℕ} (D : Database n) : Finset (Label n) :=
  open Classical in Finset.univ.filter (fun y => ∃ x, D x = some y)
def CollisionFree {n : ℕ} (D : Database n) : Prop :=
  ∀ x₁ x₂ y, D x₁ = some y → D x₂ = some y → x₁ = x₂

/-- Relabeling fixes bottom. -/
def relabel {n : ℕ} (σ : Equiv.Perm (Label n)) (D : Database n) : Database n :=
  fun x => (D x).map σ

/-- §2.3: in each cell the sum over real labels (not bottom) is zero. -/
def ValidVector {n : ℕ} (v : Database n → ℂ) : Prop :=
  ∀ (D : Database n) (x : Input n), ∑ y : Label n, v (Function.update D x (some y)) = 0

/-- An operator is valid exactly when its image is in the valid subspace. -/
def ValidMatrix {n : ℕ} (G : DBMatrix n) : Prop :=
  ∀ v : Database n → ℂ, ValidVector (G.mulVec v)
def SupportedAt {n : ℕ} (G : DBMatrix n) (t : ℕ) : Prop :=
  ∀ D₁ D₂, t < dbSize D₁ ∨ t < dbSize D₂ → G D₁ D₂ = 0
def MatrixLabelSymmetric {n : ℕ} (G : DBMatrix n) : Prop :=
  ∀ (σ : Equiv.Perm (Label n)) D₁ D₂, G (relabel σ D₁) (relabel σ D₂) = G D₁ D₂

/-- (19)–(20): coefficient matrix, with memory rows and database columns, and A†A. -/
def coefficientAt {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (t : Fin (T + 1)) :
    Matrix (Memory n W) (Database n) ℂ :=
  fun z D => compressedStateAt A t (z, D)
def gramAt {n T : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Input n) (Label n) W T) (t : Fin (T + 1)) : DBMatrix n :=
  (coefficientAt A t).conjTranspose * coefficientAt A t

/-- (21) and (23): PSD square root and its entrywise Born joint law. -/
def sqrtGram {n : ℕ} (G : DBMatrix n) : DBMatrix n := CFC.sqrt G
def jointLaw {n : ℕ} (G : DBMatrix n) (p : Database n × Database n) : ℝ :=
  Complex.normSq (sqrtGram G p.1 p.2)
def databaseInformation {n : ℕ} (G : DBMatrix n) : ℝ := mutualInfoBits (jointLaw G)

/-- Definition 4.3 and (59): all three expectations use the standard database second. -/
def capacity {n : ℕ} (G : DBMatrix n) : ℝ :=
  open Classical in ∑ D : Database n, if CollisionFree D then (dbSize D : ℝ) * (G D D).re else 0
def matchedCount {n : ℕ} (G : DBMatrix n) : ℝ :=
  open Classical in ∑ Dₜ : Database n, ∑ D : Database n,
    jointLaw G (Dₜ, D) * (if CollisionFree D then ((dbRange D ∩ dbRange Dₜ).card : ℝ) else 0)
def unmatchedCount {n : ℕ} (G : DBMatrix n) : ℝ :=
  open Classical in ∑ Dₜ : Database n, ∑ D : Database n,
    jointLaw G (Dₜ, D) * (if CollisionFree D then ((dbRange D \ dbRange Dₜ).card : ℝ) else 0)

end CompressedOracleDuality.LabelSymmetric


