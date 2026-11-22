-- Prove2me | Definitions.Def_LeanPool_PureNock_PaperNames
-- name    : LeanPool_PureNock_PaperNames
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:29:56.611659+00:00
-- url     : https://prove2.me/theorems/21090517-3103-4438-8ddc-f122de6783a2
-- title:
--   Paper Names
-- statement:
--   Definitions and structural lemmas for Paper Names, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperNames.lean

module
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Definitions.Def_LeanPool_PureNock_NounValidation
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Theorems.Thm_Nock_BTree_dyck_iff_encode
public import Theorems.Thm_Nock_Noun_Validation
public import Theorems.Thm_Nock_Noun_decomp
public import Theorems.Thm_Nock_Noun_pbt_size
public import Theorems.Thm_Nock_Noun_pbt_size_of_size
public import Theorems.Thm_Nock_Verb_deterministic_Trace
public import Theorems.Thm_Nock_Verb_deterministic_Trace_strict
public import Theorems.Thm_Nock_Verb_domain
public import Theorems.Thm_Nock_Verb_equiv_continuations
public import Theorems.Thm_Nock_Verb_finite_of_valid_or_invalid
public import Theorems.Thm_P2M_Nock_Verb_equiv_continuations__1f39d28d1128

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace NockPure
alias «Def:Proper_BT» := Nock.BTree
alias «Def:tree_nodes» := Nock.Noun.internal
alias «Lem:pbt_size» := Nock.Noun.pbt_size_of_size
alias «Lem:optimal_dyck» := Nock.BTree.dyck_iff_encode
alias «Def:noun» := Nock.Noun
alias «Def:verb» := Nock.Verb
alias «Algorithm:Opcode_Updates_verb» := Nock.Verb.redex
alias «Def:NockProgram» := Nock.Verb.IsNockProgram
alias «Def:eval_trace» := Nock.Verb.Consistent
alias «Def:Nock» := Nock.Verb.FiniteΛ
alias «Corr:valid_invalid_finite» := Nock.Verb.finite_of_valid_or_invalid
alias «Lem:domain» := Nock.Verb.domain
alias «lemma:equiv_continuations» := Nock.Verb.equiv_continuationsΛ
alias «Thm:deterministic_Trace» := Nock.Verb.deterministic_Trace_strict
alias «Lem:decomp» := Nock.Noun.decomp
alias «Algorithm:Valid_Noun» := Nock.checkValidNoun
alias «Thm:Noun_Validation» := Nock.Noun_Validation
alias «Algorithm:Noun_Operators» := Nock.Verb.reduce
alias «Algorithm:Unroll_Operator» := Nock.Verb.reduce
alias «Algorithm:Transition_Function» := Nock.Verb.NockCheck
end NockPure


