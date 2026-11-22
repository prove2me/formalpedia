-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:08.155762+00:00
-- url     : https://prove2.me/theorems/73c544f8-56af-467a-addb-889835900cb2
-- title:
--   Gam Lead
-- statement:
--   Definitions and structural lemmas for Gam Lead, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamLead.lean

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset
section
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]
noncomputable def wf (m : σ →₀ ℕ) : K := ∏ x, ((m x).factorial : K)
noncomputable def fk (F G : MvPolynomial σ K) : K :=
  ∑ m ∈ F.support, F.coeff m * G.coeff m * wf m
end
section tie
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)
end tie
section real
variable {σ : Type} [Fintype σ] [DecidableEq σ]
end real
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
section
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
variable (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe
end
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
section
variable {K σ : Type} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe
end
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open Finset
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
noncomputable def kap0 (o n z t r : ℕ) : ℝ :=
  ((z + t).choose t : ℝ) / ((o + n + r + z - 1).choose t : ℝ) *
    ((t.factorial * (o + n + r - 1 - t).descFactorial t : ℕ) : ℝ)
noncomputable def Kc (o z : ℕ) : ℝ :=
  ∑ L ∈ range (o + 1), (((z + L).choose L * L.factorial * L.factorial : ℕ) : ℝ)
section
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe
end
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
section gen
variable (K : Type) [Field K]
noncomputable def fSub {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) :
    Fin N × Fin r → MvPolynomial (Fin (N + 1) × Fin r) K :=
  fun ⟨i, c⟩ =>
    if LL.vec i then
      (if c = ρ then ∑ c', X (Fin.castSucc i, c') * X (Fin.last N, c')
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c))
    else
      (if c = ρ then X (Fin.last N, ρ) * X (Fin.castSucc i, ρ)
       else X (Fin.last N, ρ) * X (Fin.castSucc i, c) - X (Fin.castSucc i, ρ) * X (Fin.last N, c))
noncomputable def frz {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin N × Fin r) K) : MvPolynomial (Fin (N + 1) × Fin r) K :=
  X (Fin.last N, ρ) ^ (n - LL.total) * aeval (fSub K LL ρ) f
noncomputable def gamK {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (z n : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) K) : K :=
  (((LL.deg (Fin.last N) + n + r + z - 1).choose (LL.deg (Fin.last N)) : ℕ) : K) *
    fk (Formalism.GM.tiePhi (fun c : Fin r => (Fin.castSucc (Fin.last N), c)) (fun c : Fin r => (Fin.last (N + 1), c))
      ((LL.snoc n).deg (Fin.castSucc (Fin.last N))) ((LL.snoc n).deg (Fin.last (N + 1))) z
      (frz K LL ρ n f)) (frz K LL ρ n f') /
    ((((n - LL.total).factorial * LL.total.factorial : ℕ) : K) * ∏ i, ((LL.deg i).factorial : K))
end gen
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
section bh
variable {K σ : Type} [Field K] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
end bh
section frz
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)
abbrev wW : Fin r → Fin (N + 1 + 1) × Fin r := fun c => (Fin.castSucc (Fin.last N), c)
abbrev eη : Fin r → Fin (N + 1 + 1) × Fin r := fun c => (Fin.last (N + 1), c)
noncomputable def sq (m : Fin (N + 1) × Fin r →₀ ℕ) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K :=
  ∏ x, fSub K LL ρ x ^ (Finsupp.update m (Fin.last N, ρ) 0) x
end frz
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
section
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)
end
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
section gen
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]
variable (P : σ → Prop) [DecidablePred P]
noncomputable def kill : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval (fun v => if P v then (0 : MvPolynomial σ K) else X v)
end gen
section frz
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)
def Pη (ρ : Fin r) (v : Fin (N + 1 + 1) × Fin r) : Prop := v.1 = Fin.last (N + 1) ∧ v.2 ≠ ρ
instance (ρ : Fin r) : DecidablePred (Pη (N := N) ρ) := fun v => by unfold Pη; infer_instance
def cs' : Fin (N + 1) × Fin r → Fin (N + 1 + 1) × Fin r := fun x => (Fin.castSucc x.1, x.2)
end frz
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open Filter Topology Finset
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
section
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ)
noncomputable def V0 (m : Fin (N + 1) × Fin r →₀ ℕ) (n : ℕ) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K :=
  if m (Fin.last N, ρ) = e then X (Fin.last (N + 1), ρ) ^ (n - LL.total) * sq LL ρ m else 0
noncomputable def Yh (m : Fin (N + 1) × Fin r →₀ ℕ) (n : ℕ) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K :=
  if m (Fin.last N, ρ) = e then 0
  else (tieE (wW (N := N)) eη ^ (m (Fin.last N, ρ) - e - 1)) (X (Fin.last (N + 1), ρ) ^ (n - LL.total) * sq LL ρ m)
noncomputable def gv (m : Fin (N + 1) × Fin r →₀ ℕ) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K :=
  (tieE (wW (N := N)) eη ^ (m (Fin.last N, ρ) - e)) (sq LL ρ m)
noncomputable def gF (m : Fin (N + 1) × Fin r →₀ ℕ) : MvPolynomial (Fin (N + 1 + 1) × Fin r) K :=
  if m (Fin.last N, ρ) = e then tieF (wW (N := N)) eη (sq LL ρ m) else 0
variable (hv : LL.vec (Fin.last N) = true) (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m)
  (hme : e ≤ m (Fin.last N, ρ)) (n : ℕ) (hn : LL.total ≤ n)
include hm hme hn
end
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM Filter Topology
section
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]
end
section
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)
noncomputable def inMono (e : ℕ) (m : Fin (N + 1) × Fin r →₀ ℕ) : MvPolynomial (Fin (N + 1) × Fin r) K :=
  if m (Fin.last N, ρ) = e then monomial m 1 else 0
end
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM Filter Topology
section
variable {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)
end
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM Filter Topology
section
variable {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)
end
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
section
variable (K : Type) [Field K] [CharZero K]
local notation "ι" => algebraMap ℚ K
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)
end
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
section
variable {K : Type} [Field K]
end
end Formalism.GM.leadingTermLemmas
namespace Formalism.GM
open MvPolynomial Finset Filter Topology Formalism.GM.leadingTermLemmas
end Formalism.GM


