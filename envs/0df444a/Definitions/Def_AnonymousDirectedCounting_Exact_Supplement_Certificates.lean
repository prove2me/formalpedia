-- Prove2me | Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_Certificates
-- name    : AnonymousDirectedCounting_Exact_Supplement_Certificates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:51:03.739912+00:00
-- url     : https://prove2.me/theorems/6cd6c2ef-79eb-426e-bc53-af2b72ab574e
-- title:
--   Full history-prefix certificates, binary storage and individual causal support
-- statement:
--   A full-prefix certificate lists every history node through the final round, including hidden nodes, with its parent, outdegree, positive red multiplicities and positive anonymity. All numbers, node ids, list lengths and delimiters are included in its self-delimiting binary encoding. A designated bottom identifies the observed vista; its decoded history must equal the input vista, equivalently its backward closure is the same labeled vista.
--
--   For an input vista $\mathcal V$, leader count $\ell$ and candidate order $N$, validity checks the table syntax, total anonymity $N$ at every level, exactly $\ell$ leaders at level zero, child-anonymity conservation and the full flow equations. When $N>1$, it also checks positive incoming and outgoing degree and strong connectivity of the new-node digraph of Lemma 11; when $N=1$, balance alone suffices. Status is inherited along parents. These are finite table checks, with no assumed physical realization. A separate semantic relation identifies every full level and anonymity with those of an actual network.
--
--   The **individual causal support** of an observer $x$ at round $t$ is
--   $$\Gamma_t=\{x\},\qquad\Gamma_{r-1}=\Gamma_r\cup\{y:\exists z\in\Gamma_r,\ e_r(y,z)>0\}.$$
--   It concerns individual agents, and can be smaller than the union of visible fibers. Only indices $0\le r\le t$ are allowed.
--
--   The certificate is the explicit object behind the compressed-prefix and fixed-order NP statements. Its mathematical decoding may use the published recursive history values; its bit length counts only the stored finite tables, never an unfolded history or individual parallel arcs.
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Appendix B, printed p. 18 (PDF p. 20); Appendix E.3–E.5, printed pp. 25–27 (PDF pp. 27–29)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_Vistas
import Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_Rounds

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact.Supplement

open AnonymousDirectedCounting.Exact
open scoped Classical

noncomputable section

/-- Individual causal support from Appendix B, used in E.2. Only levels `0 ≤ r ≤ t`
are allowed. At level `t` it is `{x}`; a backward step retains the current agents and adds
all senders into them in that round. It is not the union of visible fibers. -/
def causalSupport {N : ℕ} (G : NetworkModel N) (t : ℕ) (x : Fin N)
    (r : Fin (t + 1)) : Finset (Fin N) :=
  Nat.rec {x} (fun k support => support ∪ Finset.univ.filter
    (fun y => ∃ z ∈ support, 0 < G.arcs (t - k) y z)) (t - r.val)

/-- Full-prefix tables of E.3–E.5. `data` uses the vista table's storage format, now listing
ALL nodes, including hidden ones, and a designated bottom. `weights` lists one positive binary
anonymity per node. Full-table validity does not demand that every node is visible. -/
structure FullPrefixCertificate where
  data : VistaTable
  weights : List (ℕ × ℕ)

namespace FullPrefixCertificate

def weight (C : FullPrefixCertificate) (v : ℕ) : ℕ :=
  (C.weights.lookup v).getD 0

/-- Pure finite-table syntax, without an assumed physical realization. -/
def Syntax (C : FullPrefixCertificate) : Prop :=
  let T := C.data
  T.levels.length = T.depth + 1 ∧ T.levels.flatten.Nodup ∧
  T.bottom ∈ T.level T.depth ∧
  (T.status.map Prod.fst).Perm (T.level 0) ∧
  (T.status.filter (fun p => p.2)).length ≤ 1 ∧
  (T.status.filter (fun p => !p.2)).length ≤ 1 ∧
  (T.parents.map Prod.fst).Perm (T.levels.drop 1).flatten ∧
  (∀ r, ∀ v ∈ T.level (r + 1), T.parentOf v ∈ T.level r) ∧
  (T.reds.map (fun e => (e.1, e.2.1))).Nodup ∧
  (∀ e ∈ T.reds, 0 < e.2.2 ∧ ∃ r, e.1 ∈ T.level r ∧ e.2.1 ∈ T.level (r + 1)) ∧
  (∀ r, ∀ v ∈ T.level (r + 1), ∀ w ∈ T.level (r + 1), v ≠ w →
    T.parentOf v = T.parentOf w →
      (T.degreeOf v, fun u => T.mult u v) ≠ (T.degreeOf w, fun u => T.mult u w)) ∧
  (C.weights.map Prod.fst).Perm T.levels.flatten ∧
  ∀ v ∈ T.levels.flatten, 0 < C.weight v

/-- The checks of Lemma 13: total order and leader count, disjoint refinement, full flow,
Lemma 11's positive-degree and node-path tests when `N > 1`, and the designated bottom's
backward closure equal to the input vista. Inherited status is supplied by `decodeNode`.
No network realization or correctness of a verifier is assumed here. -/
def ValidFor (C : FullPrefixCertificate) (T : VistaTable) (ell N : ℕ) : Prop :=
  C.Syntax ∧ T.WellFormed ∧ 0 < ell ∧ 0 < N ∧ C.data.depth = T.depth ∧
  (∀ r, r ≤ C.data.depth → ((C.data.level r).map C.weight).sum = N) ∧
  (((C.data.level 0).filter (fun v => C.data.statusOf v)).map C.weight).sum = ell ∧
  (∀ r, r < C.data.depth → ∀ u ∈ C.data.level r,
    (((C.data.level (r + 1)).filter (fun v => C.data.parentOf v = u)).map C.weight).sum =
      C.weight u) ∧
  (∀ r, r < C.data.depth → ∀ u ∈ C.data.level r,
    (((C.data.level (r + 1)).filter (fun v => C.data.parentOf v = u)).map
      (fun v => C.weight v * C.data.degreeOf v)).sum =
    ((C.data.level (r + 1)).map (fun w => C.weight w * C.data.mult u w)).sum) ∧
  (∀ r, r < C.data.depth → 1 < N →
    (∀ v ∈ C.data.level (r + 1), 0 < C.data.degreeOf v ∧
      0 < ((C.data.level r).map (fun u => C.data.mult u v)).sum) ∧
    PathConnected (fun v w : {i : ℕ // i ∈ C.data.level (r + 1)} =>
      0 < C.data.degreeOf v.val ∧ 0 < C.data.mult (C.data.parentOf v.val) w.val)) ∧
  HEq C.data.decode T.decode

/-- Semantic link: all listed nodes, parents, labels and anonymities describe precisely the
actual full history prefix of `G`. Equal decoded histories identify the vista's labeled nodes;
no expanded history is stored in the binary encoding. -/
def Represents {N : ℕ} (C : FullPrefixCertificate) (G : NetworkModel N) : Prop :=
  ∀ r, r ≤ C.data.depth →
    ((C.data.level r).map (C.data.decodeNode r)).Nodup ∧
    ((C.data.level r).map (C.data.decodeNode r)).toFinset = historyLevel G r ∧
    ∀ v ∈ C.data.level r, C.weight v = anonymity G r (C.data.decodeNode r v)

/-- Actual self-delimiting binary storage: the full node/edge table, then one binary anonymity
for each node. Parents, ids, depth, bottom and all list delimiters are included in this length. -/
def encode (C : FullPrefixCertificate) : List Bool :=
  encodeVistaTable C.data ++ encodeNat C.weights.length ++
    C.weights.flatMap (fun p => encodeNat p.1 ++ encodeNat p.2)

end FullPrefixCertificate

end

end AnonymousDirectedCounting.Exact.Supplement


