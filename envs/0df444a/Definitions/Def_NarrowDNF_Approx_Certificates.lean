-- Prove2me | Definitions.Def_NarrowDNF_Approx_Certificates
-- name    : NarrowDNF_Approx_Certificates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:43.400147+00:00
-- url     : https://prove2.me/theorems/8353b0b4-6c90-4c08-8f73-07b97ab9ac63
-- title:
--   Positive certificates and the specified truncated DNF
-- statement:
--   A coordinate set $T$ is a positive certificate for $u$ if every $y$ equal to one on $T$ satisfies $u(y)=1$. For any activation family, define
--   $$T(x)=\{i\in A_J(x):x_i=1\}.$$
--   For every natural $w$, define the finite family and its disjunction by exactly Eq. (7):
--   $$g_w(y)=\bigvee_{x:u(x)=1,\ |T(x)|\le w}\ \bigwedge_{i\in T(x)}y_i.$$
--   Repeated equal terms are removed by finite-set image. This does not change the formula or width. The definition itself imposes no monotonicity or certificate hypothesis and promises no approximation property; those are the assertions of Lemma 4.1.
--
--   The explicit construction includes $w=0$, the empty family when there are no qualifying inputs, and empty terms when an accepted input has no active one-coordinates.
-- source:
--   Chenghua Liu, Boning Meng, STOC 2027 submission #1509 (October 2026), Lemma 4.1, Eq. (7), p. 8 (PDF p. 9)

import Definitions.Def_NarrowDNF_Approx_Activation
import Definitions.Def_NarrowDNF_Approx_DNF

namespace NarrowDNF.Approx

def PositiveCertificate {n : ℕ} (u : Cube n → Bool) (T : Finset (Fin n)) : Prop :=
  ∀ y, (∀ i ∈ T, y i = true) → u y = true

noncomputable def activeOnes {n : ℕ} (J : ActivationFamily n) (x : Cube n) :
    Finset (Fin n) := (activeUnion J x).filter (fun i => x i = true)

/-- Exactly Eq. (7): terms from all accepted inputs whose active 1-set is short. -/
noncomputable def truncatedDNF {n : ℕ} (J : ActivationFamily n) (u : Cube n → Bool)
    (w : ℕ) : DNF n := by
  classical
  exact (Finset.univ.filter (fun x => u x = true ∧ (activeOnes J x).card ≤ w)).image
    (activeOnes J)

end NarrowDNF.Approx


